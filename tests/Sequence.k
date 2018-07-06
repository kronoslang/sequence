Import "Sequence.k"

Package Test {
	Use Sequence

	Take-Skip = { Format:Text(Take(#10 Skip(#5 Range:Count(1 2)))) }
	Array-Cycle = { Format:Text(Take(#30 Array-Cycle[1 2 3 2 1])) }
	Lazy-Map = { Format:Text(Take(#10 Map((* 3) Range:Count(1 2)))) }
	Infinite-Sugar = { Format:Text(Range:Count(1 1)) }
}