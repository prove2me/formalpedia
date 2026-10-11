-- Prove2me | solution 1 for KruskalAnalysis.call_complete
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T00:05:04.672339+00:00
-- url     : https://prove2.me/submissions/15bbe85b-fc46-4a4e-b63e-a6d1296c1431

import Definitions.Def_Algo_kruskal_Analysis
import Theorems.Thm_KruskalAnalysis_scan_contract
import Theorems.Thm_SortIndicesAnalysis_call
import Theorems.Thm_UnionFindAnalysis_constructor_summary
import Theorems.Thm_UnionFindAnalysis_constructor_rep
import Theorems.Thm_Algo2Lean_Kruskal_Scan_minimum_spanning_forest


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Reusable contracts for the compiled union-find implementation.

`find_contract` and `union_contract` give the exact model, storage, and clock
effects of full path compression and union by rank. `find_amortized` and
`union_amortized` bound incremental work using a shared inverse-Ackermann
potential. The simpler `find_summary` and `union_summary` retain logarithmic
worst-case bounds, partition guarantees, and protection for caller storage.

The forest and rank invariants are independent of generated code and graphs.
Constructor correctness is in the companion `union_find_init` analysis. Costs
count the explicit source clocks and compose from arbitrary initial counters.
-/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated


















open Algo2Lean.UnionFind (State Find compress    )





/-- Charging a clock does not change the represented data structure. -/
theorem Rep.tick {heap : Heap} {layout : Layout} {n : Nat} {model : State n}
    (representation : Rep heap layout model) (clock : String) (amount : Nat := 1) :
    Rep (heap.tick clock amount) layout model :=
  ⟨representation.valid, representation.object, representation.readParent,
    representation.readRank, representation.readSize, representation.parentAllocated,
    representation.rankAllocated, representation.separate, representation.parents,
    representation.ranks⟩

















































































-- Main result: Correctness and running time


end UnionFindAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Construction of the reusable rank-and-compression disjoint-set structure.
The constructor allocates one object and two arrays, initializes singleton
components, and charges exactly `n + 1` initialization ticks. -/

namespace UnionFindAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.union_find Algo.union_find.Algo2LeanGenerated







































/-- Initializing parents preserves every other sequence. -/
theorem initializeEntries_other (heap : Heap) (parent other : SeqRef)
    (first : Int) (count : Nat) (different : other ≠ parent) :
    (initializeEntries heap parent first count).read other = heap.read other := by
  induction count generalizing heap first with
  | zero => rfl
  | succ count ih =>
    rw [initializeEntries, ih]
    funext index
    simp [Heap.read, Heap.write, different]





/-- Each initialized entry contributes one tick and changes no other clock. -/
theorem initializeEntries_clocks (heap : Heap) (parent : SeqRef)
    (first : Int) (count : Nat) (clock : String) :
    (initializeEntries heap parent first count).clocks clock =
      heap.clocks clock + if clock = "uf_init" then count else 0 := by
  induction count generalizing heap first with
  | zero => simp [initializeEntries]
  | succ count ih =>
    rw [initializeEntries, ih]
    by_cases same : clock = "uf_init" <;> simp [Heap.tick, same, Nat.add_assoc, Nat.add_comm]







/-- The constructor charges exactly one initial tick plus one per vertex. -/
theorem constructor_clocks (heap : Heap) (size : Nat) (clock : String) :
    (newHeap heap size).clocks clock = heap.clocks clock +
      if clock = "uf_init" then size + 1 else 0 := by
  simp only [newHeap, initializedHeap, initializeEntries_clocks]
  by_cases same : clock = "uf_init" <;>
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.tick, same, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Constructor allocation adds exactly two integer sequences and one object,
    and leaves the collection allocation boundary unchanged. -/
theorem constructor_allocations (heap : Heap) (size : Nat) :
    (newHeap heap size).nextRef = heap.nextRef + 2 ∧
    (newHeap heap size).nextObject = heap.nextObject + 1 ∧
    (newHeap heap size).nextCollection = heap.nextCollection := by
  simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
    set_UnionFind_size, Nat.add_assoc]

/-- All old storage survives construction; the new arrays and object are fresh. -/
theorem constructor_frame (heap : Heap) (size : Nat) :
    (∀ ref, ref < heap.nextObject → (newHeap heap size).objects ref = heap.objects ref) ∧
    (∀ ref, ref < heap.nextRef → (newHeap heap size).read ref = heap.read ref) ∧
    (newHeap heap size).collections = heap.collections := by
  refine ⟨?_, ?_, ?_⟩
  · intro ref old
    simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size, Heap.writeField, Heap.allocateObject, Nat.ne_of_lt old]
  · intro ref old
    have different : ref ≠ heap.nextRef := Nat.ne_of_lt old
    simp only [newHeap, initializedHeap, Heap.allocateObject_nextRef,
      initializeEntries_other _ _ _ _ _ different]
    funext index
    simp [prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank, set_UnionFind_size,
      Heap.read, Heap.allocate, different, show ref ≠ heap.nextRef + 1 by omega]
  · simp [newHeap, initializedHeap, prepareInitialHeap, set_UnionFind_parent, set_UnionFind_rank,
      set_UnionFind_size]

-- Main result: Correctness and running time







/-- All existing storage is framed out of construction. Its object and arrays
    are fresh allocations, so its modification footprint is empty. -/
theorem constructor_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (newHeap heap size) [] [] [] := by
  obtain ⟨objects, sequences, collections⟩ := constructor_frame heap size
  obtain ⟨nextRef, nextObject, nextCollection⟩ := constructor_allocations heap size
  refine ⟨by rw [nextRef]; omega, by rw [nextObject]; omega, by simp only [nextCollection, Nat.le_refl],
    ?_, ?_, ?_, ?_, ?_⟩
  · intro ref old
    simp only [Heap.objectClass, objects ref old]
  · intro ref old
    simp only [Heap.sequenceType, collections]
  · intro ref old _
    exact sequences ref old
  · intro ref old _
    exact objects ref old
  · intro ref old _
    rw [collections]





end UnionFindAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Finite undirected graph mathematics for Kruskal's algorithm. Edge identities
separate parallel input occurrences. Endpoints and weights are integers; weights
may be negative. This module does not depend on a union-find implementation or
on generated algorithm definitions.
-/

namespace Algo2Lean.Kruskal















theorem Connected.mono {before after : List Edge} {u v : Int}
    (subset : ∀ edge ∈ before, edge ∈ after) (path : Connected before u v) :
    Connected after u v := by
  induction path with
  | refl => exact .refl _
  | step edge path ih =>
    obtain ⟨e, member, direction⟩ := edge
    exact .step ⟨e, subset e member, direction⟩ ih


















































































/-- Reordering input occurrences changes neither connectivity nor spanning. -/
theorem Spans.perm_input {before after selected : List Edge} (spanning : Spans before selected)
    (same : before.Perm after) : Spans after selected := by
  constructor
  · exact fun edge member => same.mem_iff.mp (spanning.subset edge member)
  · exact fun u v path => spanning.connected u v
      (path.mono (fun _ member => same.mem_iff.mpr member))

theorem MinimumSpanningForest.perm_input {before after selected : List Edge}
    (minimum : MinimumSpanningForest before selected) (same : before.Perm after) :
    MinimumSpanningForest after selected :=
  ⟨minimum.1, minimum.2.1.perm_input same,
    fun other forest spanning => minimum.2.2 other forest (spanning.perm_input same.symm)⟩

/-- Sorting may permute edge occurrences freely, including equal-weight edges.
    The result remains a minimum spanning forest of the original input. -/
theorem Scan.minimum_of_perm {input sorted result : List Edge}
    (permutation : input.Perm sorted) (ordered : Sorted sorted)
    (scan : Scan sorted [] result) : MinimumSpanningForest input result :=
  (scan.minimum_spanning_forest ordered).perm_input permutation.symm















end Algo2Lean.Kruskal

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal initializes singleton components, sorts edge identifiers, and compares
representatives before selecting an edge and applying the verified union.
The graph argument is independent of the storage and transition machinery.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal Algo.kruskal.Algo2LeanGenerated
open UnionFindAnalysis
open Algo2Lean.Kruskal










































/-- The source entry point allocates the empty result, constructs singleton
    components, sorts the edges, and enters the explicitly named edge loop. -/
theorem kruskal_calls (heap initialized sorted final : Heap)
    (size count : Int) (sources targets weights order : SeqRef) (sets : UnionFindAnalysis.Layout)
    (valid : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (construction : Algo.union_find.UnionFind.Call (heap.allocate (fun _ => 0)) size initialized sets.object)
    (sorting : Algo.sort_indices.sort_indices.Call initialized (weights, count) sorted order)
    (scan : ScanCall ⟨sets, sources, targets, order, heap.nextRef⟩ (sorted.tick "kruskal") 0 count final) :
    kruskal.Call heap (size, sources, targets, weights, count) final heap.nextRef := by
  refine ⟨valid, ?_⟩
  intro caller
  apply Reaches.prepend (Step.kruskal_pc39 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc38 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc37 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc36 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc35 _ _ _)
  apply (ModuleCall.summary import_0_simulates _ caller construction.2).trans
  apply Reaches.prepend (Step.kruskal_pc34 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc33 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc32 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc31 _ _ _)
  apply (ModuleCall.summary import_2_simulates _ caller sorting.2).trans
  apply Reaches.prepend (Step.kruskal_pc30 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc29 _ _ _)
  apply Reaches.prepend (Step.kruskal_pc28 _ _ _)
  refine scan (.active _ (.fn_kruskal 4 _) []) ?_ rfl caller
  exact ⟨True.intro, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
/-- A finite array prefix determines the inductive order view. -/
theorem Order.of_indexed (heap : Heap) (ref : SeqRef) (index : Int) (pending : List Edge)
    (agreement : ∀ (i : Nat) (within : i < pending.length),
      heap.read ref (index + i) = (pending[i].id : Int)) : Order heap ref index pending := by
  induction pending generalizing index with
  | nil => exact .nil index
  | cons edge pending ih =>
    apply Order.cons
    · simpa using agreement 0 (by simp)
    · apply ih (index + 1)
      intro i within
      have shifted := agreement (i + 1) (by simpa using within)
      have indexEq : index + (↑(i + 1) : Int) = index + 1 + i := by omega
      rw [indexEq] at shifted
      simpa only [List.getElem_cons_succ] using shifted

/-- A disjoint-set representation survives a call that preserves existing
    storage. This is the only fact about sorting needed by the union-find model. -/
theorem Rep.preserve {n : Nat} {before after : Heap} {layout : UnionFindAnalysis.Layout}
    {model : Algo2Lean.UnionFind.State n} (rep : Rep before layout model)
    (frame : before.Footprint after [] [] []) : Rep after layout model := by
  open Algo.union_find.Algo2LeanGenerated in
    have object : is_UnionFind after layout.object :=
      ⟨Nat.lt_of_lt_of_le rep.object.1 frame.nextObject,
        (frame.classes layout.object rep.object.1).trans rep.object.2⟩
    refine ⟨rep.valid, object, ?_, ?_, ?_,
      Nat.lt_of_lt_of_le rep.parentAllocated frame.nextRef,
      Nat.lt_of_lt_of_le rep.rankAllocated frame.nextRef, rep.separate, ?_, ?_⟩
    · simpa only [field_UnionFind_parent, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readParent
    · simpa only [field_UnionFind_rank, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readRank
    · simpa only [field_UnionFind_size, if_pos object,
        frame.readField layout.object rep.object.1 (by simp), if_pos rep.object] using rep.readSize
    · intro vertex
      rw [frame.read layout.parent rep.parentAllocated (by simp)]
      exact rep.parents vertex
    · intro vertex
      rw [frame.read layout.rank rep.rankAllocated (by simp)]
      exact rep.ranks vertex





/-- Initialization preserves every caller location while creating private data. -/
theorem initial_footprint (heap : Heap) (size : Nat) :
    heap.Footprint (initialHeap heap size) [] [] [] :=
  ((Heap.Footprint.refl heap [] [] []).allocate (fun _ => 0)).trans
    (constructor_footprint (heap.allocate (fun _ => 0)) size)

/-- Initialization preserves all previously allocated sequence values. -/
theorem initial_read_old (heap : Heap) (size : Nat) (ref : SeqRef) (old : ref < heap.nextRef) :
    (initialHeap heap size).read ref = heap.read ref :=
  (initial_footprint heap size).read ref old (by simp)

/-- Sorting protects the initialized components and empty result flags. -/
theorem initial_invariant (heap sorted : Heap) (size : Nat) (sources targets order : SeqRef)
    (pending : List Edge)
    (sourceAllocated : sources < heap.nextRef) (targetAllocated : targets < heap.nextRef)
    (frame : (initialHeap heap size).Footprint sorted [] [] [])
    (fresh : (initialHeap heap size).nextRef ≤ order) (orderAllocated : order < sorted.nextRef)
    (bounds : ValidInput size pending)
    (sourceValues : ∀ edge ∈ pending, heap.read sources edge.id = edge.source)
    (targetValues : ∀ edge ∈ pending, heap.read targets edge.id = edge.target)
    (ordering : ∀ (i : Nat) (within : i < pending.length), sorted.read order i = (pending[i].id : Int)) :
    ScanInvariant size (initialLayout heap size sources targets order) (sorted.tick "kruskal")
      (Algo2Lean.UnionFind.initial size) 0 pending [] := by
  have refs : (initialHeap heap size).nextRef = heap.nextRef + 3 := by
    simpa [initialHeap, Heap.allocate] using (constructor_allocations (heap.allocate (fun _ => 0)) size).1
  have initFrame := initial_footprint heap size
  have whole := initFrame.trans frame
  have chosenInit : heap.nextRef < (initialHeap heap size).nextRef := by rw [refs]; omega
  have chosenValues : (initialHeap heap size).read heap.nextRef = (fun _ => 0) := by
    have preserve := (constructor_frame (heap.allocate (fun _ => 0)) size).2.1 heap.nextRef (by simp [Heap.allocate])
    change (newHeap (heap.allocate (fun _ => 0)) size).read heap.nextRef = _
    rw [preserve]
    funext index
    exact Heap.read_allocate_new heap (fun _ => 0) index
  have represented := Rep.preserve (constructor_rep (heap.allocate (fun _ => 0)) size) frame
  refine ⟨represented.tick "kruskal", ?_,
    (fun edge member => ⟨bounds.source edge member, bounds.target edge member⟩), ?_, ?_, ?_, ?_,
    Nat.lt_of_lt_of_le sourceAllocated whole.nextRef,
    Nat.lt_of_lt_of_le targetAllocated whole.nextRef, orderAllocated,
    Nat.lt_of_lt_of_le chosenInit frame.nextRef, ?_, ?_, ?_, ?_⟩
  · intro u v
    rw [Algo2Lean.UnionFind.initial_connected, connected_nil]
    constructor
    · intro same; subst v; rfl
    · intro same; apply Fin.ext; omega
  · intro edge member
    change sorted.read sources edge.id = edge.source
    rw [whole.read sources sourceAllocated (by simp)]
    exact sourceValues edge member
  · intro edge member
    change sorted.read targets edge.id = edge.target
    rw [whole.read targets targetAllocated (by simp)]
    exact targetValues edge member
  · apply Order.of_indexed
    intro i within
    change sorted.read order (0 + i) = _
    simpa only [Int.zero_add] using ordering i within
  · intro id
    change sorted.read heap.nextRef id = _
    rw [frame.read heap.nextRef chosenInit (by simp), chosenValues]
    simp
  all_goals
    simp only [initialLayout, newLayout, Heap.allocate_nextRef, List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega

/-- Constructing all singleton components costs V+1 initialization ticks. -/
theorem initial_work (heap : Heap) (size : Nat) :
    work (initialHeap heap size).clocks = work heap.clocks + size + 1 := by
  simp [work, UnionFindAnalysis.work, initialHeap, constructor_clocks]
  omega

/-- Initialization changes only the union-find initialization clock. -/
theorem initial_clocks (heap : Heap) (size : Nat) (clock : String)
    (notInit : clock ≠ "uf_init") :
    (initialHeap heap size).clocks clock = heap.clocks clock := by
  simp [initialHeap, constructor_clocks, notInit]

end KruskalAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The graph supplied to the source program consists of three integer sequences
and a finite edge count. This module translates that representation into the
finite graph model and connects the reusable sorting theorem to Kruskal's scan.
-/

open Algo2LeanGenerated Algo2Lean.Kruskal

namespace KruskalInput











/-- Distinct positions give distinct edge identities, including parallel edges. -/
theorem edges_unique (sources targets weights : Seq) (count : Int) :
    ((edges sources targets weights count).map Edge.id).Nodup := by
  rw [edges_ids]
  exact List.nodup_range

/-- Membership connects the graph model back to the original endpoint arrays. -/
theorem edge_contents {sources targets weights : Seq} {count : Int} {edge : Edge}
    (member : edge ∈ edges sources targets weights count) :
    (edge.id : Int) < count ∧ sources edge.id = edge.source ∧
      targets edge.id = edge.target ∧ weights edge.id = edge.weight := by
  obtain ⟨identifier, present, rfl⟩ := List.mem_map.mp member
  obtain ⟨nonnegative, within⟩ := (Algo2Lean.FiniteIndex.range_member count identifier).mp present
  simpa only [edgeAt, Int.toNat_of_nonneg nonnegative] using
    (show identifier < count ∧ sources identifier = sources identifier ∧
      targets identifier = targets identifier ∧ weights identifier = weights identifier from
      ⟨within, rfl, rfl, rfl⟩)

theorem WellFormed.valid {size count : Int} {sources targets : Seq}
    (input : WellFormed size count sources targets) (weights : Seq) :
    ValidInput size.toNat (edges sources targets weights count) := by
  refine ⟨edges_unique _ _ _ _, ?_, ?_⟩
  · intro edge member
    obtain ⟨within, source, target, weight⟩ := edge_contents member
    have bound := input.source_bounds edge.id (by omega) within
    rw [source] at bound
    exact ⟨bound.1, by omega⟩
  · intro edge member
    obtain ⟨within, source, target, weight⟩ := edge_contents member
    have bound := input.target_bounds edge.id (by omega) within
    rw [target] at bound
    exact ⟨bound.1, by omega⟩



/-- Sort the identifiers once, then obtain the sorted graph view without
    unfolding the sorting algorithm or repeating a heap proof. -/
theorem sorted_edges (sources targets weights order : Seq) (count : Int)
    (sorting : SortIndicesAnalysis.SortedPermutation weights count order) :
    ∃ pending, SortedEdges sources targets weights order count pending := by
  obtain ⟨identifiers, permutation, sorted, agreement⟩ := sorting
  let pending := identifiers.map (edgeAt sources targets weights)
  have mapped : (edges sources targets weights count).Perm pending := permutation.symm.map _
  have memberContents (edge : Edge) (member : edge ∈ pending) :=
    edge_contents (mapped.mem_iff.mpr member)
  refine ⟨pending, mapped, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sorted.map (edgeAt sources targets weights) (by intros; assumption)
  · exact mapped.length_eq.symm.trans (edges_length _ _ _ _)
  · intro index within
    have bound : index < identifiers.length := by simpa [pending] using within
    have original : identifiers[index] ∈ Algo2Lean.FiniteIndex.range count :=
      permutation.mem_iff.mp (List.getElem_mem bound)
    have nonnegative := ((Algo2Lean.FiniteIndex.range_member _ _).mp original).1
    have agrees := agreement index bound
    simpa [pending, edgeAt, getElem!_pos, bound, Int.toNat_of_nonneg nonnegative] using agrees
  · exact fun edge member => (memberContents edge member).2.1
  · exact fun edge member => (memberContents edge member).2.2.1
  · exact fun edge member => (memberContents edge member).2.2.2
  · exact fun edge member => (memberContents edge member).1

theorem SortedEdges.valid {size count : Int} {sources targets weights order : Seq} {pending : List Edge}
    (sorting : SortedEdges sources targets weights order count pending)
    (input : WellFormed size count sources targets) : ValidInput size.toNat pending := by
  constructor
  · exact (input.valid weights).identities.perm (sorting.permutation.map Edge.id)
  · intro edge member
    exact (input.valid weights).source edge (sorting.permutation.mem_iff.mpr member)
  · intro edge member
    exact (input.valid weights).target edge (sorting.permutation.mem_iff.mpr member)

/-- The scan's graph theorem applies directly to the original array input. -/
theorem SortedEdges.minimum {sources targets weights order : Seq} {count : Int}
    {pending selected : List Edge}
    (sorting : SortedEdges sources targets weights order count pending)
    (scan : Scan pending [] selected) : MinimumSpanningForest (edges sources targets weights count) selected :=
  scan.minimum_of_perm sorting.permutation sorting.sorted






end KruskalInput

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's algorithm on finite undirected weighted graphs. The public interface
uses integer sequences for source vertices, target vertices, edge weights, and
returned selection flags. Correctness and running time reuse the independent
sorting, union-find, and graph analyses.
-/

namespace KruskalAnalysis

open Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
open KruskalInput





private theorem sorting_work {before after : Heap} {count : Int}
    (budget : SortIndicesAnalysis.Budget count (2 * count.toNat) before after) :
    SortIndicesAnalysis.runtime after.clocks ≤ SortIndicesAnalysis.runtime before.clocks +
      SortIndicesAnalysis.runtimeBound count.toNat := by
  have source := budget "sort_steps"
  have comparisons := budget "heap_comparisons"
  have swaps := budget "heap_swaps"
  simp [SortIndicesAnalysis.rate] at source comparisons swaps
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have rates : 3 * (count.toNat + 1).log2 + 2 =
      1 + 2 * (count.toNat + 1).log2 + ((count.toNat + 1).log2 + 1) := by omega
  unfold SortIndicesAnalysis.runtimeBound
  rw [rates]
  simp only [BinaryModuleAnalysis.depth, Nat.mul_add, Nat.mul_one] at source comparisons swaps ⊢
  omega

private theorem sorting_preserves_work {before after : Heap}
    (preserved : SortIndicesAnalysis.Preserves before after) : work after.clocks = work before.clocks := by
  simp only [work, UnionFindAnalysis.work]
  rw [preserved.clocks "uf_init" (by decide) (by decide) (by decide),
    preserved.clocks "uf_find" (by decide) (by decide) (by decide),
    preserved.clocks "uf_compress" (by decide) (by decide) (by decide),
    preserved.clocks "uf_union" (by decide) (by decide) (by decide),
    preserved.clocks "kruskal" (by decide) (by decide) (by decide)]

private theorem scan_preserves_sorting (heap final : Heap)
    (clocks : ∀ clock, clock ∉ ["kruskal", "uf_find", "uf_compress", "uf_union"] →
      final.clocks clock = (heap.tick "kruskal").clocks clock) :
    SortIndicesAnalysis.runtime final.clocks = SortIndicesAnalysis.runtime heap.clocks := by
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [clocks "sort_steps" (by decide), clocks "heap_comparisons" (by decide),
    clocks "heap_swaps" (by decide)]
  simp [Heap.tick]

private theorem initialization_preserves_sorting (heap : Heap) (size : Nat) :
    SortIndicesAnalysis.runtime (initialHeap heap size).clocks =
      SortIndicesAnalysis.runtime heap.clocks := by
  simp only [SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [initial_clocks _ _ _ (by decide), initial_clocks _ _ _ (by decide),
    initial_clocks _ _ _ (by decide)]

/-- The sorter protects every previously allocated caller location. -/
private theorem sorting_footprint {before after : Heap}
    (preserved : SortIndicesAnalysis.Preserves before after) : before.Footprint after [] [] [] := by
  refine ⟨preserved.refs, preserved.objectRefs, by simp [preserved.collectionRefs], ?_, ?_, ?_, ?_, ?_⟩
  · intro ref old
    simp only [Heap.objectClass, preserved.objects ref old]
  · intro ref old
    simp only [Heap.sequenceType, preserved.collections]
  · intro ref old _
    exact preserved.sequences ref old
  · intro ref old _
    exact preserved.objects ref old
  · intro ref old _
    rw [preserved.collections]



/-- The algorithm terminates on every finite valid graph. Its output flags name
    a minimum spanning forest, and its clocks satisfy the explicit cost bound.
    Sequence references permit aliasing among the three input arrays. -/
theorem call_complete (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef := by
  let initialized := initialHeap heap size.toNat
  have initFrame := initial_footprint heap size.toNat
  obtain ⟨sorted, order, sortCall, sortedIds, preserved, fresh, orderAllocated, budget⟩ :=
    SortIndicesAnalysis.call initialized weights count
      (Nat.lt_of_lt_of_le allocated.2.2 initFrame.nextRef) input.count_nonnegative
  have sameWeights : initialized.read weights = heap.read weights :=
    initial_read_old heap size.toNat weights allocated.2.2
  rw [sameWeights] at sortedIds
  obtain ⟨pending, sorting⟩ := sorted_edges (heap.read sources) (heap.read targets)
    (heap.read weights) (sorted.read order) count sortedIds
  have sortFrame := sorting_footprint preserved
  have initial := initial_invariant heap sorted size.toNat sources targets order pending
    allocated.1 allocated.2.1 sortFrame fresh orderAllocated (sorting.valid input)
    sorting.source sorting.target sorting.order
  obtain ⟨final, model, selected, scanCall, finalInvariant, scan, frame, clocks, worstCase, bound⟩ :=
    scan_contract (initialLayout heap size.toNat sources targets order)
      (sorted.tick "kruskal") (Algo2Lean.UnionFind.initial size.toNat) 0 count pending []
      initial (by rw [sorting.length]; have nonnegative := input.count_nonnegative; omega)
  have composed := kruskal_calls heap initialized sorted final size count sources targets weights order
    (UnionFindAnalysis.newLayout (heap.allocate (fun _ => 0))) allocated
    (by simpa only [initialized, initialHeap, UnionFindAnalysis.newLayout,
      Int.toNat_of_nonneg input.size_nonnegative] using!
      UnionFindAnalysis.constructor_summary (heap.allocate (fun _ => 0)) size.toNat)
    sortCall scanCall
  have prefixFrame := (initFrame.trans sortFrame).tick "kruskal"
  have wholeFrame := (prefixFrame.weaken
    (moreSequences := [(initialLayout heap size.toNat sources targets order).sets.parent,
      (initialLayout heap size.toNat sources targets order).sets.rank,
      (initialLayout heap size.toNat sources targets order).chosen])
    (moreObjects := []) (moreCollections := []) (by simp) (by simp) (by simp)).trans frame
  refine ⟨final, heap.nextRef, selected, composed, sorting.minimum scan, finalInvariant.flags,
    ?_, ?_, Nat.le_refl _, finalInvariant.chosenAllocated⟩
  · have sortBound := sorting_work budget
    have unchangedWork := sorting_preserves_work preserved
    have unchangedSort := scan_preserves_sorting sorted final clocks
    have unchangedInitSort := initialization_preserves_sorting heap size.toNat
    have initialWork := initial_work heap size.toNat
    have tickWork : work (sorted.tick "kruskal").clocks = work sorted.clocks + 1 := by
      simp [work, UnionFindAnalysis.work, Heap.tick]; omega
    rw [tickWork, unchangedWork, sorting.length, Algo2Lean.UnionFind.initial_potential] at bound
    change work initialized.clocks = _ at initialWork
    change SortIndicesAnalysis.runtime initialized.clocks = _ at unchangedInitSort
    simp only [runtime, runtimeBound]
    rw [unchangedSort]
    omega
  · refine ⟨wholeFrame.nextRef, wholeFrame.nextObject, wholeFrame.nextCollection,
      wholeFrame.classes, wholeFrame.types, ?_, wholeFrame.otherObjects, wholeFrame.otherCollections⟩
    intro ref old _
    apply wholeFrame.otherSequences ref old
    simp only [initialLayout, UnionFindAnalysis.newLayout, Heap.allocate_nextRef,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    simp only [SeqRef] at *
    omega



















-- Main result: Correctness


-- Main result: Running time




end KruskalAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights : Algo2LeanGenerated.SeqRef),
      Algo.kruskal.kruskal.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count)))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          Exists.{1} fun final =>
            Exists.{1} fun chosen =>
              Exists.{1} fun selected =>
                Algo.kruskal.kruskal.Call heap
                    (Prod.mk.{0, 0} size
                      (Prod.mk.{0, 0} sources (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
                    final chosen ∧
                  Algo2Lean.Kruskal.MinimumSpanningForest
                      (KruskalInput.edges (heap.read sources) (heap.read targets) (heap.read weights)
                        count)
                      selected ∧
                    KruskalAnalysis.Flags (final.read chosen) selected ∧
                      LE.le.{0} (KruskalAnalysis.runtime final.clocks)
                          (HAdd.hAdd.{0, 0, 0} (KruskalAnalysis.runtime heap.clocks)
                            (KruskalAnalysis.runtimeBound size.toNat count.toNat)) ∧
                        heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                          LE.le.{0} heap.nextRef chosen ∧ LT.lt.{0} chosen final.nextRef :=
  KruskalAnalysis.call_complete
