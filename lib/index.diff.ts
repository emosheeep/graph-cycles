import { ShortTree } from 'short-tree'
import { RotatedArraySet } from 'rotated-array-set'
import { compare } from 'fast-string-compare'
import { setWith, get } from 'lodash'
import { uniq, uniqArrays, walk } from './util.js'
import {
	Graph,
	FullAnalysisResult,
	FastAnalysisResult,
} from './types.js'
export * from './types.js'
export { sortFullAnalysisResult, sortFastAnalysisResult } from './util.js'

const pathSymbolMap: Record<string, string> = {};
let pathSymbol = 0;
const toPathSymbol = (path: string): string => {
	if (path in pathSymbolMap) {
		return pathSymbolMap[path];
	}
	const symbol = pathSymbol++;
	pathSymbolMap[path] = String(symbol);
	pathSymbolMap[symbol] = path;
	return String(pathSymbol);
};
const toPathValue = (symbol: string): string => {
	return pathSymbolMap[symbol];
};

// Removes duplicate edges (they are ignored), and ensures single
function buildAndEnsureValidGraph( edges: Graph )
{
	return new Map(
		edges.map( ( [ from, to ] ) => [ toPathSymbol( from ), uniq( to ).map( toPathSymbol ) ] )
	);
}

export function analyzeGraph( graph: Graph )
: FullAnalysisResult
{
	const graphMap = buildAndEnsureValidGraph( graph );

	const entrypoints = new ShortTree( compare );
	const cycleNodes = new Set< string >( );
	const cycles = new RotatedArraySet< string >( );
	const dependencies = new Set< string >( );
	const allExitPaths = {};

	const recordCycleEntrypoint = ( path: Array< string > ) =>
	{
		if ( path.length === 0 )
			return;
		entrypoints.insert( path );
	};

	const recordCycle = ( path: Array< string > ) =>
	{
		if ( cycles.add( path.map(toPathValue) ) )
		{
			for ( const node of path )
				cycleNodes.add( toPathValue( node ) );
		}
	};

	const isPartOfCycle = ( node: string ): boolean => cycleNodes.has( node );

	// Traverse from each possible entrypoint
	for ( const [ from, _to ] of graphMap.entries( ) )
	{
		if (!_to.length) continue;
		const path = [ from ];
		const visited = new Set< string >( );
		let foundCycle = false;
		let createdCycle = false;
		const exitPaths = {};

		// Traversal
		let to = _to;
		let nodeNextIndex = 0;

		const getLeaf = ( ) => path[ path.length - 1 ];

		// Return true if we should turn around the traversal, if we've
		// entered a known cycle from a non-cycle entrypoint.
		const testNode = ( ): boolean =>
		{
			const node = getLeaf( );

			const shouldCheckCycles = !createdCycle;

			if ( shouldCheckCycles && isPartOfCycle( node ) )
			{
				recordCycleEntrypoint( path.slice( 0, -1 ) );

				foundCycle = true;
				return true;
			}

			// Cycled back to itself
			if ( visited.has( node ) )
			{
				// Record entrypoint to cycle
				const entrypointPath = path.slice(
					0,
					path.indexOf( node ) + 1
				);
				// Only record entrypoints if there's at least one node
				// *before* the cycle begins
				if ( entrypointPath.length > 1 )
					recordCycleEntrypoint( entrypointPath.slice( 0, -1 ) );

				const cycle = path.slice( path.indexOf( node ), -1 );

				recordCycle( cycle );

				createdCycle = true;
				return true;
			}

			return false;
		};

		// Returns true if walking down was successful
		const walkDown = ( ): boolean =>
		{
			if ( nodeNextIndex >= to.length )
				return false;

			const node = getLeaf( );
			visited.add( node );

			const nextLeaf = to[ nodeNextIndex ];
			path.push( nextLeaf );
			to = graphMap.get( nextLeaf ) ?? [ ];
			nodeNextIndex = 0;
			return true;
		};

		// Returns true if walking up is not possible anymore (root is reached)
		const walkUp = ( ): boolean =>
		{
			if ( path.length === 1 )
				return true;

			const lastLeaf = getLeaf( );
			path.pop( );
			const node = getLeaf( );
			visited.delete( node );
			to = graphMap.get( node ) ?? [ ];
			nodeNextIndex = to.indexOf( lastLeaf ) + 1;

			if ( nodeNextIndex >= to.length )
				return walkUp( );
			else
				walkDown( );

			return false;
		};

		while ( true )
		{
			if ( testNode( ) )
			{
				if ( walkUp( ) )
					break;
				else
					continue;
			}

			if ( walkDown( ) )
				continue;

			// Save path up to this exitpoint.
			// If the path along the way here was part of a cycle, its
			// detection will mark this exitpoint as a dependence.
			const dotPath = path.join( '.' );
			const parentDotPath =
				path.length === 1 ? dotPath : path.slice(0, -1).join('.');
			const pathObject = {
				...get(exitPaths, dotPath, {}),
				[path[path.length - 1]]: {},
			};
			setWith(exitPaths, parentDotPath, pathObject, Object);

			if ( walkUp( ) )
				break;
		}

		// If cycles were found, test exit nodes against cycles to find
		// dependencies
		if ( foundCycle || createdCycle )
			walk(exitPaths, [], path =>
			{
				while (
					path.length > 0 &&
					!isPartOfCycle( path[ path.length - 1 ] )
				)
				{
					dependencies.add( path[ path.length - 1 ] );
					path.pop( );
				}
			} );
		// for ( const path of exitPaths )
		//   path.length && nestedPathTryAdd(allExitPaths, path );
	}

	// There might be cycles found as part of an entrypoint *after* the
	// entrypoint was detected. Chop them off at the time of entering a cycle.
	const trimmedEntrypoints = uniqArrays(
			entrypoints.values( )
			.map( path =>
			{
				for ( let i = 0; i < path.length; ++i )
				{
					if ( isPartOfCycle( path[ i ] ) )
					{
						path = path.slice( 0, i );
						break;
					}
				}
				return path;
			} )
			.filter( path => path.length > 0 )
		);

	const all = new Set( [ ...cycleNodes, ...trimmedEntrypoints.flat( ) ] );

	const dependenciesList =
		[ ...dependencies ].filter( dep => !all.has( dep ) );

	const allInclDeps = new Set( [ ...all, ...dependenciesList ] );

	const dependents = new Set< string >( );
	allExitPaths.forEach( path =>
	{
		if ( path.length > 0 && allInclDeps.has( path[ path.length - 1 ] ) )
		{
			const prePath = path.slice( 0, -1 );
			if ( prePath.some( node => allInclDeps.has( node ) ) )
				return;
			// This is a free floating path leading up to a dependency of
			// cyclic nodes
			prePath.forEach( node => dependents.add( node ) );
		}
	} );

	return {
		cycles: cycles.values( ),
		entrypoints:
			trimmedEntrypoints as FullAnalysisResult[ 'entrypoints' ],
		dependencies: dependenciesList,
		dependents: [ ...dependents ],
		all: [ ...all ],
	};
}

export function analyzeGraphFast( graph: Graph ): FastAnalysisResult
{
	const graphMap = buildAndEnsureValidGraph( graph );

	const cycleNodes = new Set< string >( );
	const dependencies = new Set< string >( );
	const dependents = new Set< string >( );
	const exitPaths: Array< Array< string > > = [ ];

	const recordCycle = ( path: Array< string > ) =>
	{
		for ( const node of path )
			cycleNodes.add( node );
	};

	const isPartOfCycle = ( node: string ): boolean =>
		cycleNodes.has( node );

	// Traverse from each possible entrypoint
	for ( const [ from, _to ] of graphMap.entries( ) )
	{
		const path = [ from ];
		const visited = new Set< string >( );

		// Traversal
		let to = _to;
		let nodeNextIndex = 0;

		const getLeaf = ( ) => path[ path.length - 1 ];

		// Return true if we should turn around the traversal, if we've
		// entered a known cycle from a non-cycle entrypoint.
		const testNode = ( ): boolean =>
		{
			const node = getLeaf( );

			if ( isPartOfCycle( node ) )
			{
				// Is any other node up to this point part of a cycle,
				// the whole path from that point is
				recordCycle( path.slice( 0, -1 ) );

				return true;
			}

			// Cycled back to itself
			if ( visited.has( node ) )
			{
				const cycle = path.slice( 0, -1 );

				recordCycle( cycle );

				return true;
			}

			return false;
		};

		// Returns true if walking down was successful
		const walkDown = ( ): boolean =>
		{
			if ( nodeNextIndex >= to.length )
				return false;

			const node = getLeaf( );
			visited.add( node );

			const nextLeaf = to[ nodeNextIndex ];
			path.push( nextLeaf );
			to = graphMap.get( nextLeaf ) ?? [ ];
			nodeNextIndex = 0;
			return true;
		};

		// Returns true if walking up is not possible anymore (root is reached)
		const walkUp = ( ): boolean =>
		{
			if ( path.length === 1 )
				return true;

			const lastLeaf = getLeaf( );
			path.pop( );
			const node = getLeaf( );
			visited.delete( node );
			to = graphMap.get( node ) ?? [ ];
			nodeNextIndex = to.indexOf( lastLeaf ) + 1;

			if ( nodeNextIndex >= to.length )
				return walkUp( );
			else
				walkDown( );

			return false;
		};

		while ( true )
		{
			if ( testNode( ) )
			{
				if ( walkUp( ) )
					break;
				else
					continue;
			}

			if ( walkDown( ) )
				continue;

			// Save path up to this exitpoint.
			// If the path along the way here was part of a cycle, its
			// detection will mark this exitpoint as a dependence.
			exitPaths.push( [ ...path ] );

			if ( walkUp( ) )
				break;
		}
	}

	// Find dependencies
	exitPaths.forEach( origPath =>
	{
		const path = [ ...origPath ];

		const localPath: Array< string > = [ ];
		while (
			path.length > 0 &&
			!isPartOfCycle( path[ path.length - 1 ] )
		)
		{
			localPath.push( path[ path.length - 1 ] );
			path.pop( );
		}
		if ( path.length > 0 )
			// There is a cycle before, so it's an exit path (not a completely uncyclic cluster)
			localPath.forEach( segment => dependencies.add( segment ) );
	} );

	const all = new Set< string >( [ ...dependencies, ...cycleNodes ] );

	// Find dependents
	exitPaths.forEach( path =>
	{
		if ( path.length > 0 && all.has( path[ path.length - 1 ] ) )
		{
			const prePath = path.slice( 0, -1 );
			if ( prePath.some( node => all.has( node ) ) )
				return;
			// This is a free floating path leading up to a dependency of
			// cyclic nodes
			prePath.forEach( node => dependents.add( node ) );
		}
	} );

	return {
		cyclic: [ ...cycleNodes ],
		dependencies: [ ...dependencies ]
			.filter( dep => !cycleNodes.has( dep ) ),
		dependents: [ ...dependents ]
			.filter( dep => !cycleNodes.has( dep ) ),
	};
}
