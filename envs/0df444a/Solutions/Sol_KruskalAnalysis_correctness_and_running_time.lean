-- Prove2me | solution 1 for KruskalAnalysis.correctness_and_running_time
-- status  : ACCEPTED   (prove)
-- author  : @lunjia
-- created : 2026-10-11T02:03:18.011475+00:00
-- url     : https://prove2.me/submissions/8c57697e-7688-46df-8fad-53dfd783b437

import Definitions.Def_Algo_kruskal_Analysis_SortedRevision
import Theorems.Thm_KruskalAnalysis_total_call_contract


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

























theorem ack_succ (level value : Nat) :
    ack (level + 1) value = iterate (ack level) (value + 1) value := rfl







theorem ack_le_succ (level value : Nat) : ack level value ≤ ack (level + 1) value := by
  exact iterate_mono_count (fun x => Nat.le_of_lt (ack_gt level x))
    (Nat.succ_le_succ (Nat.zero_le value)) value

theorem ack_mono_left {first second : Nat} (ordered : first ≤ second) (value : Nat) :
    ack first value ≤ ack second value := by
  induction second generalizing first with
  | zero =>
    have zero : first = 0 := by omega
    simp [zero]
  | succ second ih =>
    by_cases same : first = second + 1
    · subst first; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (ack_le_succ second value)















theorem alpha_min {n level : Nat} (positive : 0 < level) (smaller : level < alpha n) :
    ack level 1 ≤ n := by
  have minimal := (Classical.choose_spec (inverse_exists n)).2 level smaller
  omega

theorem alpha_le {n level : Nat} (positive : 0 < level) (large : n < ack level 1) :
    alpha n ≤ level := by
  by_cases ordered : alpha n ≤ level
  · exact ordered
  · have := alpha_min positive (by omega : level < alpha n)
    omega













end Algo2Lean.Ackermann

end

section
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true



/-!
Arithmetic bounds for the two Kruskal running-time statements. The sorting
term and vertex initialization absorb the inverse-Ackermann contribution,
even when the graph has many isolated vertices. These lemmas depend only on
the existing Ackermann definition; they do not inspect an algorithm or heap.
-/

namespace KruskalBounds

open Algo2Lean.Ackermann

private theorem iterate_successor (count value : Nat) :
    iterate (fun n => n + 1) count value = value + count := by
  induction count with
  | zero => simp
  | succ count ih => simp [iterate_succ, ih, Nat.add_assoc]

private theorem ack_one (value : Nat) : ack 1 value = 2 * value + 1 := by
  change iterate (fun n => n + 1) (value + 1) value = 2 * value + 1
  rw [iterate_successor]
  omega

/-- Hierarchy growth dominates powers of two in the hierarchy index. -/
theorem exponential_le_ack (level : Nat) : 2 ^ level ≤ ack level 1 := by
  induction level with
  | zero => simp
  | succ level ih =>
    by_cases zero : level = 0
    · subst level
      decide
    · have double := ack_mono_left (by omega : 1 ≤ level) (ack level 1)
      rw [ack_one] at double
      have step : ack (level + 1) 1 = ack level (ack level 1) := by
        simp [ack_succ, iterate]
      rw [step, Nat.pow_succ]
      omega

/-- The inverse-Ackermann factor is bounded by a binary logarithm. -/
theorem alpha_le_log (vertices : Nat) :
    alpha vertices ≤ (vertices + 1).log2 + 1 := by
  apply alpha_le (by omega)
  have threshold := exponential_le_ack ((vertices + 1).log2 + 1)
  have powerBound : vertices + 1 < 2 ^ ((vertices + 1).log2 + 1) := Nat.lt_log2_self
  omega

/-- A logarithmic vertex factor can be paid by vertex initialization and the
    edge-sorting scale. This does not require a relationship between V and E. -/
theorem logarithm_absorption (vertices edges : Nat) :
    edges * (vertices + 1).log2 ≤
      2 * (vertices + 1) + edges * (edges + 1).log2 := by
  by_cases ordered : (vertices + 1).log2 ≤ (edges + 1).log2
  · have multiplied := Nat.mul_le_mul_left edges ordered
    omega
  · have gap : (vertices + 1).log2 =
        (edges + 1).log2 + ((vertices + 1).log2 - (edges + 1).log2) := by omega
    have edgePower : edges ≤ 2 ^ ((edges + 1).log2 + 1) := by
      have : edges + 1 < 2 ^ ((edges + 1).log2 + 1) := Nat.lt_log2_self
      omega
    have differencePower : (vertices + 1).log2 - (edges + 1).log2 ≤
        2 ^ ((vertices + 1).log2 - (edges + 1).log2) :=
      Nat.le_of_lt Nat.lt_two_pow_self
    have multiplied := Nat.mul_le_mul edgePower differencePower
    have powers : 2 ^ ((edges + 1).log2 + 1) *
        2 ^ ((vertices + 1).log2 - (edges + 1).log2) =
        2 * 2 ^ (vertices + 1).log2 := by
      rw [← Nat.pow_add]
      have exponent : (edges + 1).log2 + 1 +
          ((vertices + 1).log2 - (edges + 1).log2) = (vertices + 1).log2 + 1 := by omega
      rw [exponent, Nat.pow_succ, Nat.mul_comm]
    rw [powers] at multiplied
    have vertexPower := Nat.mul_le_mul_left 2 (Nat.log2_self_le (by omega : vertices + 1 ≠ 0))
    have sum : edges * (vertices + 1).log2 = edges * (edges + 1).log2 +
        edges * ((vertices + 1).log2 - (edges + 1).log2) := by
      calc
        edges * (vertices + 1).log2 = edges * ((edges + 1).log2 +
            ((vertices + 1).log2 - (edges + 1).log2)) := congrArg (edges * ·) gap
        _ = _ := Nat.mul_add _ _ _
    omega

/-- Union-find's inverse-Ackermann work fits within the total sorting scale. -/
theorem alpha_absorption (vertices edges : Nat) :
    edges * alpha vertices ≤
      2 * (vertices + 1) + 2 * (edges * (edges + 1).log2) := by
  by_cases zero : edges = 0
  · simp [zero]
  · have logarithmPositive : 1 ≤ (edges + 1).log2 :=
      (Nat.le_log2 (by omega)).mpr (by simp; omega)
    have edgeBound := Nat.mul_le_mul_left edges logarithmPositive
    have alphaBound := Nat.mul_le_mul_left edges (alpha_le_log vertices)
    have logarithmBound := logarithm_absorption vertices edges
    simp only [Nat.mul_add, Nat.mul_one] at alphaBound edgeBound
    omega

/-- The explicit eight-clock budget has a uniform O(V + E log(E+1) + 1)
    upper bound, including empty and disconnected graphs. -/
theorem total_budget_le (vertices edges : Nat) :
    2 * edges * (3 * (edges + 1).log2 + 2) + vertices + 2 +
      edges * (10 * alpha vertices + 14) ≤
        44 * (vertices + 1 + edges * (edges + 1).log2) := by
  by_cases zero : edges = 0
  · simp only [zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_add, Nat.mul_one]
    omega
  · have logarithmPositive : 1 ≤ (edges + 1).log2 :=
      (Nat.le_log2 (by omega)).mpr (by simp; omega)
    have edgeBound := Nat.mul_le_mul_left edges logarithmPositive
    have amortizedBound := Nat.mul_le_mul_left 10 (alpha_absorption vertices edges)
    simp only [Nat.mul_one] at edgeBound
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at amortizedBound ⊢
    have e3 : edges * (3 * (edges + 1).log2) = 3 * (edges * (edges + 1).log2) := by
      simp only [Nat.mul_left_comm]
    have e10 : edges * (10 * alpha vertices) = 10 * (edges * alpha vertices) := by
      simp only [Nat.mul_left_comm]
    omega

end KruskalBounds

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







/-- One constant controls every finite graph, with no density assumption. -/
theorem runtimeBound_le (vertices edges : Nat) :
    runtimeBound vertices edges ≤ 44 * runtimeScale vertices edges := by
  simpa only [runtimeBound, runtimeScale, SortIndicesAnalysis.runtimeBound,
    KruskalSortedAnalysis.runtimeBound, Nat.add_assoc] using
    KruskalBounds.total_budget_le vertices edges

















-- Main result: Running time (total)
/-- The full source algorithm returns a minimum spanning forest with total
    recorded work O(V + E log(E+1) + 1). The positive constant is independent
    of every input and initial counter; no inverse-Ackermann term remains in
    this total scale. Output freshness and caller storage are also guaranteed. -/
theorem correctness_and_running_time :
    ∃ C : Nat, 0 < C ∧
    ∀ (heap : Heap) (size count : Int) (sources targets weights : SeqRef),
      kruskal.ValidInput heap (size, sources, targets, weights, count) →
      WellFormed size count (heap.read sources) (heap.read targets) →
      ∃ final chosen selected,
        kruskal.Call heap (size, sources, targets, weights, count) final chosen ∧
        MinimumSpanningForest (edges (heap.read sources) (heap.read targets) (heap.read weights) count) selected ∧
        Flags (final.read chosen) selected ∧
        heap.Footprint final [] [] [] ∧ heap.nextRef ≤ chosen ∧ chosen < final.nextRef ∧
        heap.Increments final (Heap.cost heap final) ∧
        runtime (Heap.cost heap final) ≤ C * runtimeScale size.toNat count.toNat := by
  refine ⟨44, by decide, ?_⟩
  intro heap size count sources targets weights allocated input
  obtain ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments, bound⟩ :=
    total_call_contract heap size count sources targets weights allocated input
  exact ⟨final, chosen, selected, execution, minimum, flags, frame, fresh, valid, increments,
    Nat.le_trans bound (runtimeBound_le _ _)⟩

















-- Main result: Correctness






-- Main result: Running time (after sorting)


end KruskalAnalysis

end

set_option autoImplicit false
theorem solution :
    Exists.{1} fun C =>
      LT.lt.{0} (0 : Nat) C ∧
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
                          (Prod.mk.{0, 0} sources
                            (Prod.mk.{0, 0} targets (Prod.mk.{0, 0} weights count))))
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
                                  LE.le.{0} (KruskalAnalysis.runtime (heap.cost final))
                                    (HMul.hMul.{0, 0, 0} C
                                      (KruskalAnalysis.runtimeScale size.toNat count.toNat)) :=
  KruskalAnalysis.correctness_and_running_time
