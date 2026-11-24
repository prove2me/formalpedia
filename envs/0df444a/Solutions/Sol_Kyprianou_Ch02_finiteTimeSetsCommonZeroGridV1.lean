-- Prove2me | solution 1 for Kyprianou.Ch02.finiteTimeSetsCommonZeroGridV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:27:47.539141+00:00
-- url     : https://prove2.me/submissions/3dc8dabb-9672-4846-8d3b-ac512c979720

import Mathlib
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (I J : Finset ℝ≥0) :
    ∃ (n : ℕ) (t : Fin (n+1) → ℝ≥0), Monotone t ∧ t 0 = 0 ∧
      (∀ i : I, ∃ k, t k = i) ∧ (∀ j : J, ∃ k, t k = j) := by

  classical
  let S := I ∪ J
  let n := S.card
  let e := S.orderEmbOfFin (rfl : S.card = n)
  let t : Fin (n+1) → ℝ≥0 := Fin.cases 0 e
  refine ⟨n,t,?_,rfl,?_,?_⟩
  · intro i j hij
    cases i using Fin.cases with
    | zero => exact zero_le
    | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j => exact e.monotone (by exact Nat.le_of_succ_le_succ hij)
  · intro i
    let x : S := ⟨i, Finset.mem_union_left J i.2⟩
    refine ⟨((S.orderIsoOfFin rfl).symm x).succ,?_⟩
    change (S.orderEmbOfFin rfl) ((S.orderIsoOfFin rfl).symm x) = i
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  · intro j
    let x : S := ⟨j, Finset.mem_union_right I j.2⟩
    refine ⟨((S.orderIsoOfFin rfl).symm x).succ,?_⟩
    change (S.orderEmbOfFin rfl) ((S.orderIsoOfFin rfl).symm x) = j
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
