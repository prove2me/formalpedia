-- Prove2me | solution 1 for KruskalAnalysis.total_call_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T01:55:44.181617+00:00
-- url     : https://prove2.me/submissions/91733700-589c-4bdc-a179-418afd528901

import Definitions.Def_Algo_kruskal_Analysis_SortedRevision
import Theorems.Thm_KruskalSortedAnalysis_call_complete
import Theorems.Thm_SortIndicesAnalysis_call


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock monotonicity certificates for reusable union-find and sorting components.
Imported algorithms retain their own certificates; client proofs only compose them.
-/

namespace DataStructureClocks

open Algo2LeanCore Algo2LeanGenerated



/-- The binary heap's arithmetic, mutation, and explicit ticks never lower a clock. -/
theorem heap_step {before after : Algo.indexed_heap.Algo2LeanGenerated.Configuration}
    (transition : Algo.indexed_heap.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> intro clock
  all_goals try simp only [resume_heap]
  all_goals simp [Config.heap, Heap.tick,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_vertices,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_positions,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_keys,
      Algo.indexed_heap.Algo2LeanGenerated.set_MinHeap_size] <;> split <;> omega

/-- The union-find implementation preserves clock monotonicity through recursion. -/
theorem union_find_step {before after : Algo.union_find.Algo2LeanGenerated.Configuration}
    (transition : Algo.union_find.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> intro clock
  all_goals try simp only [resume_heap]
  all_goals simp [Config.heap, Heap.tick,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_parent,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_rank,
      Algo.union_find.Algo2LeanGenerated.set_UnionFind_size] <;> split <;> omega

/-- Sorting reuses the binary heap certificate at imported transitions. -/
theorem sort_step {before after : Algo.sort_indices.Algo2LeanGenerated.Configuration}
    (transition : Algo.sort_indices.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap, Heap.tick] <;> split <;> omega
  case import_0 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! heap_step delegated

end DataStructureClocks

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock counters are monotone through every transition, including delegated calls.
These certificates make cost increments usable with arbitrary initial clocks.
They depend only on the compiled programs, not on graph or data-structure preconditions.
-/

namespace KruskalSortedClocks

open Algo2LeanCore Algo2LeanGenerated DataStructureClocks

/-- The post-sorting scan never decreases a clock, including within union-find calls. -/
theorem kruskal_sorted_step {before after : Algo.kruskal_sorted.Algo2LeanGenerated.Configuration}
    (transition : Algo.kruskal_sorted.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap, Heap.tick] <;> split <;> omega
  case import_0 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! union_find_step delegated



end KruskalSortedClocks

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal after sorting: a caller supplies a permutation of the original edge
identifiers in nondecreasing weight order. The source allocates singleton
components and scans that order; it performs no sorting. The reusable Call
contract combines the graph exchange argument with the independently proved
inverse-Ackermann contracts for union by rank and full path compression.
-/

namespace KruskalSortedAnalysis

open Algo2LeanCore Algo2LeanGenerated
open Algo.kruskal_sorted Algo.kruskal_sorted.Algo2LeanGenerated
open Algo2Lean.Kruskal KruskalInput KruskalAnalysis









/-- Weighted runtime adds across the actual caller-relative counter increments. -/
theorem runtime_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    runtime after.clocks = runtime before.clocks + runtime costs := by
  simp only [runtime, SortIndicesAnalysis.runtime, Clocks.weighted, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, work, UnionFindAnalysis.work]
  rw [effect "sort_steps", effect "heap_comparisons", effect "heap_swaps",
    effect "uf_init", effect "uf_find", effect "uf_compress", effect "uf_union", effect "kruskal"]
  omega








-- Main result: Correctness and running time
























end KruskalSortedAnalysis

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Clock counters are monotone through every transition, including delegated calls.
These certificates make cost increments usable with arbitrary initial clocks.
They depend only on the compiled programs, not on graph or data-structure preconditions.
-/

namespace KruskalClocks

open Algo2LeanCore Algo2LeanGenerated DataStructureClocks

/-- Kruskal never decreases a clock across its own or imported transitions. -/
theorem kruskal_step {before after : Algo.kruskal.Algo2LeanGenerated.Configuration}
    (transition : Algo.kruskal.Algo2LeanGenerated.Step before after) :
    before.heap.ClocksMonotone after.heap := by
  cases transition <;> try solve
    | intro clock
      try simp only [resume_heap, ModuleCall.heap]
      simp [Config.heap] <;> split <;> omega
  case import_1 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! sort_step delegated
  case import_3 heap frame inner resume caller after delegated =>
    simpa only [ModuleCall.heap] using! KruskalSortedClocks.kruskal_sorted_step delegated

/-- Every completed call has nonnegative increments, whatever counters its
    caller accumulated before invoking Kruskal. -/
theorem call_monotone {before after : Heap} {input result}
    (execution : Algo.kruskal.kruskal.Call before input after result) :
    before.ClocksMonotone after := by
  have preserved := execution.2.root.invariant (fun state => before.ClocksMonotone state.heap)
    (Heap.ClocksMonotone.refl before)
    (fun _ _ transition accumulated => accumulated.trans (kruskal_step transition))
  exact preserved

end KruskalClocks

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
Kruskal's complete algorithm sorts edge identifiers, then calls the independently
verified sorted-edge entry point. The two runtime results distinguish the total
work from work after sorting. Both reuse the same union-by-rank and full path
compression contracts and apply from arbitrary caller counters.
-/

namespace KruskalAnalysis

open Algo2LeanCore Algo2LeanGenerated Algo.kruskal Algo2Lean.Kruskal
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

/-- The two source calls compose without inspecting either implementation. -/
theorem kruskal_calls (heap sorted final : Heap) (size count : Int)
    (sources targets weights order chosen : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (sorting : Algo.sort_indices.sort_indices.Call heap (weights, count) sorted order)
    (scanning : Algo.kruskal_sorted.kruskal_sorted.Call sorted
      (size, sources, targets, weights, count, order) final chosen)
    (resultAllocated : chosen < final.nextRef) :
    kruskal.Call heap (size, sources, targets, weights, count) final chosen := by
  open Algo.kruskal.Algo2LeanGenerated in
    refine ⟨allocated, ?_⟩
    intro caller
    apply Reaches.prepend (Step.kruskal_pc12 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc11 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc10 _ _ caller)
    apply (ModuleCall.summary import_1_simulates _ caller sorting.2).trans
    apply Reaches.prepend (Step.kruskal_pc9 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc8 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc7 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc6 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc5 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc4 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc3 _ _ caller)
    apply Reaches.prepend (Step.kruskal_pc2 _ _ caller)
    apply (ModuleCall.summary import_3_simulates _ caller scanning.2).trans
    exact Reaches.single (Step.kruskal_pc1 _ _ caller resultAllocated)

/-- Weighted runtime adds across actual caller-relative counter increments. -/
theorem runtime_increments {before after : Heap} {costs : Clocks}
    (effect : before.Increments after costs) :
    runtime after.clocks = runtime before.clocks + runtime costs :=
  KruskalSortedAnalysis.runtime_increments effect

/-- Every valid finite graph has a returning call selecting a minimum spanning
    forest. Sorting and the sorted-edge call preserve all existing caller data. -/
theorem call_complete (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      runtime final.clocks ≤ runtime heap.clocks + runtimeBound size.toNat count.toNat ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef := by
  obtain ⟨sorted, order, sortCall, sortedIds, preserved, fresh, orderAllocated, budget⟩ :=
    SortIndicesAnalysis.call heap weights count allocated.2.2 input.count_nonnegative
  have sameSources := preserved.sequences sources allocated.1
  have sameTargets := preserved.sequences targets allocated.2.1
  have sameWeights := preserved.sequences weights allocated.2.2
  have sortedInput : WellFormed size count (sorted.read sources) (sorted.read targets) := by
    simpa only [sameSources, sameTargets] using input
  have sortedValid : Algo.kruskal_sorted.kruskal_sorted.ValidInput sorted
      (size, sources, targets, weights, count, order) :=
    ⟨Nat.lt_of_lt_of_le allocated.1 preserved.refs,
      Nat.lt_of_lt_of_le allocated.2.1 preserved.refs,
      Nat.lt_of_lt_of_le allocated.2.2 preserved.refs, orderAllocated⟩
  obtain ⟨final, chosen, selected, scanCall, minimum, flags, scanBound, frame, chosenFresh,
      chosenAllocated, clocks⟩ :=
    KruskalSortedAnalysis.call_complete sorted size count sources targets weights order
      sortedValid sortedInput (by simpa only [sameWeights] using sortedIds)
  rw [sameSources, sameTargets, sameWeights] at minimum
  refine ⟨final, chosen, selected,
    kruskal_calls heap sorted final size count sources targets weights order chosen
      allocated sortCall scanCall chosenAllocated,
    minimum, flags, ?_, (sorting_footprint preserved).trans frame,
    Nat.le_trans preserved.refs chosenFresh, chosenAllocated⟩
  have sortBound := sorting_work budget
  have unchangedWork := sorting_preserves_work preserved
  simp only [runtime, KruskalSortedAnalysis.runtime] at scanBound ⊢
  unfold runtimeBound
  rw [unchangedWork] at scanBound
  omega

/-- The reusable entry-point contract includes fresh output storage, preservation
    of every existing caller location, and the actual increments of all clocks.
    It applies unchanged when called from another algorithm with nonzero clocks. -/
theorem call_contract (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, frame, fresh, allocated⟩ :=
    call_complete heap size count sources targets weights allocated input
  have increments := (KruskalClocks.call_monotone execution).increments
  refine ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, allocated, increments, ?_⟩
  rw [runtime_increments increments] at bound
  omega

/-- The complete reusable contract retains explicit coefficients for callers
    that need a numerical bound on the full algorithm. -/
theorem total_call_contract (heap : Heap) (size count : Int) (sources targets weights : SeqRef)
    (allocated : kruskal.ValidInput heap (size, sources, targets, weights, count))
    (input : WellFormed size count (heap.read sources) (heap.read targets)) :
    ∃ final chosen selected,
      kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat :=
  call_contract heap size count sources targets weights allocated input

-- Main result: Running time (total)


















-- Main result: Correctness






-- Main result: Running time (after sorting)


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
                      heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                        LE.le.{0} heap.nextRef chosen ∧
                          LT.lt.{0} chosen final.nextRef ∧
                            heap.Increments final (heap.cost final) ∧
                              LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                (KruskalAnalysis.runtimeBound size.toNat count.toNat) :=
  KruskalAnalysis.total_call_contract
