-- Prove2me | solution 1 for KruskalSortedAnalysis.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T02:03:18.493771+00:00
-- url     : https://prove2.me/submissions/66858e12-aa32-4f1d-b663-6821d95808cf

import Definitions.Def_Algo_kruskal_sorted_Analysis
import Theorems.Thm_KruskalSortedAnalysis_call_contract


section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
The Ackermann hierarchy used in the union-find amortized analysis.
`ack 0 r = r + 1` and `ack (k + 1) r` applies `ack k` exactly `r + 1`
times to `r`. The inverse `alpha n` is the least positive hierarchy index
whose value at one exceeds `n`. All arithmetic facts are independent of
program execution and of the union-find representation.
-/

namespace Algo2Lean.Ackermann















































theorem alpha_pos (n : Nat) : 0 < alpha n :=
  (Classical.choose_spec (inverse_exists n)).1.1



















end Algo2Lean.Ackermann

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







/-- The explicit bound implies O(V + E alpha(V) + 1) with one universal constant. -/
theorem runtimeBound_le (vertices edges : Nat) :
    runtimeBound vertices edges ≤ 24 * runtimeScale vertices edges := by
  have positive := Algo2Lean.Ackermann.alpha_pos vertices
  have edgeBound : 10 * Algo2Lean.Ackermann.alpha vertices + 14 ≤
      24 * Algo2Lean.Ackermann.alpha vertices := by omega
  have multiplied := Nat.mul_le_mul_left edges edgeBound
  calc
    runtimeBound vertices edges ≤ vertices + 2 + 24 * (edges * Algo2Lean.Ackermann.alpha vertices) := by
      simpa [runtimeBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
        Nat.add_le_add_left multiplied (vertices + 2)
    _ ≤ 24 * runtimeScale vertices edges := by
      simp only [runtimeScale, Nat.mul_add, Nat.mul_one]
      omega










-- Main result: Correctness and running time
/-- With edges already ordered by weight, the actual source call returns a
    minimum spanning forest in O(V + E alpha(V) + 1) recorded work. The same
    positive constant works for every graph, supplied order, and caller heap.
    The output is fresh, caller storage is preserved, and sorting costs zero. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
    ∀ (heap : Heap) (size count : Int) (sources targets weights order : SeqRef),
      kruskal_sorted.ValidInput heap (size, sources, targets, weights, count, order) →
      WellFormed size count (heap.read sources) (heap.read targets) →
      SortIndicesAnalysis.SortedPermutation (heap.read weights) count (heap.read order) →
      ∃ final chosen selected,
        kruskal_sorted.Call heap (size, sources, targets, weights, count, order) final chosen ∧
        MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
        Flags (final.read chosen) selected ∧
        heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
        heap.Increments final (Heap.cost heap final) ∧
        runtime (Heap.cost heap final) ≤ C * runtimeScale size.toNat count.toNat ∧
        (∀ clock, clock ∉ ["uf_init", "uf_find", "uf_compress", "uf_union", "kruskal"] →
          (Heap.cost heap final) clock = 0) := by
  refine ⟨24, by decide, ?_⟩
  intro heap size count sources targets weights order allocated input ordered
  obtain ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments, bound, clocks⟩ :=
    call_contract heap size count sources targets weights order allocated input ordered
  exact ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments,
    Nat.le_trans bound (runtimeBound_le _ _), clocks⟩























end KruskalSortedAnalysis

end

set_option autoImplicit false
theorem solution :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
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
                            (KruskalInput.edges (heap.read sources) (heap.read targets)
                              (heap.read weights) count)
                            selected ∧
                          KruskalAnalysis.Flags (final.read chosen) selected ∧
                            heap.Footprint final List.nil.{0} List.nil.{0} List.nil.{0} ∧
                              LE.le.{0} heap.nextRef chosen ∧
                                LT.lt.{0} chosen final.nextRef ∧
                                  heap.Increments final (heap.cost final) ∧
                                    LE.le.{0} (KruskalSortedAnalysis.runtime (heap.cost final))
                                        (HMul.hMul.{0, 0, 0} C
                                          (KruskalSortedAnalysis.runtimeScale size.toNat count.toNat)) ∧
                                      ∀ (clock : String),
                                        ¬Membership.mem.{0, 0}
                                              (List.cons.{0} "uf_init"
                                                (List.cons.{0} "uf_find"
                                                  (List.cons.{0} "uf_compress"
                                                    (List.cons.{0} "uf_union"
                                                      (List.cons.{0} "kruskal" List.nil.{0})))))
                                              clock →
                                          Eq.{1} (heap.cost final clock) (0 : Nat) :=
  KruskalSortedAnalysis.correctness_and_running_time
