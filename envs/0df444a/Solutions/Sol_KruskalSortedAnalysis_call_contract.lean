-- Prove2me | solution 1 for KruskalSortedAnalysis.call_contract
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T01:55:18.629993+00:00
-- url     : https://prove2.me/submissions/899ae710-f0db-4d66-87c3-a5a357c36f40

import Definitions.Def_Algo_kruskal_sorted_Analysis
import Theorems.Thm_KruskalSortedAnalysis_call_complete


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

/-- Every completed call has nonnegative increments, whatever counters its
    caller accumulated before invoking Kruskal. -/
theorem call_monotone {before after : Heap} {input result}
    (execution : Algo.kruskal_sorted.kruskal_sorted.Call before input after result) :
    before.ClocksMonotone after := by
  have preserved := execution.2.root.invariant (fun state => before.ClocksMonotone state.heap)
    (Heap.ClocksMonotone.refl before)
    (fun _ _ transition accumulated => accumulated.trans (kruskal_sorted_step transition))
  exact preserved

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





/-- The reusable post-sorting contract exposes actual counter increments,
    fresh output storage, unchanged caller storage, and zero sorting increments. -/
theorem call_contract (heap : Heap) (size count : Int) (sources targets weights order : SeqRef)
    (allocated : kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order))
    (input : WellFormed size count (heap.read sources) (heap.read targets))
    (ordered : SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order)) :
    ∃ final chosen selected,
      kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
      MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
      Flags (final.read chosen) selected ∧
      heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
      heap.Increments final (Heap.cost heap final) ∧
      runtime (Heap.cost heap final) ≤ runtimeBound size.toNat count.toNat ∧
      (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
        (Heap.cost heap final) clock = 0) := by
  obtain ⟨final, chosen, selected, execution, minimum, flags, bound, frame, fresh, valid, clocks⟩ :=
    call_complete heap size count sources targets weights order allocated input ordered
  have increments := (KruskalSortedClocks.call_monotone execution).increments
  refine ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments, ?_, ?_⟩
  · rw [runtime_increments increments] at bound
    omega
  · intro clock outside
    simp [Heap.cost, clocks clock outside]


-- Main result: Correctness and running time
























end KruskalSortedAnalysis

end

set_option autoImplicit false
theorem solution :
    ∀ (heap : Algo2LeanGenerated.Heap) (size count : Int)
      (sources targets weights order : Algo2LeanGenerated.SeqRef),
      Algo.kruskal_sorted.kruskal_sorted.ValidInput heap
          (Prod.mk.{0, 0} size
            (Prod.mk.{0, 0} sources
              (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights (Prod.mk.{0, 0} count order))))) →
        KruskalInput.WellFormed size count (heap.read sources) (heap.read targets) →
          SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order) →
            Exists.{1} fun final =>
              Exists.{1} fun chosen =>
                Exists.{1} fun selected =>
                  Algo.kruskal_sorted.kruskal_sorted.Call heap
                      (Prod.mk.{0, 0} size
                        (Prod.mk.{0, 0} sources
                          (Prod.mk.{0, 0} targets
                            (Prod.mk.{0, 0} weights (Prod.mk.{0, 0} count order)))))
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
                                LE.le.{0} (KruskalSortedAnalysis.runtime (heap.cost final))
                                    (KruskalSortedAnalysis.runtimeBound size.toNat count.toNat) ∧
                                  ∀ (clock : String),
                                    ¬Membership.mem.{0, 0}
                                          (List.cons.{0} "uf_init"
                                            (List.cons.{0} "uf_find"
                                              (List.cons.{0} "uf_compress"
                                                (List.cons.{0} "uf_union"
                                                  (List.cons.{0} "kruskal" List.nil.{0})))))
                                          clock →
                                      Eq.{1} (heap.cost final clock) (0 : Nat) :=
  KruskalSortedAnalysis.call_contract
