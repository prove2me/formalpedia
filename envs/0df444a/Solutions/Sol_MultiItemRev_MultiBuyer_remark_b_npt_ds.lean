-- Prove2me | solution 1 for MultiItemRev.MultiBuyer.remark_b_npt_ds
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:50:48.048792+00:00
-- url     : https://prove2.me/submissions/45d10455-92af-44be-a2a1-4fc74719867d

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.MultiBuyer in
theorem solution {n : ℕ} (hn : 1 ≤ n) {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (Fin n → ι → ℝ≥0)) [IsProbabilityMeasure μ] :
    (∀ M : MechanismN n ι, IsAdmissibleDS M →
      (IsNPTN M ↔ ∀ (x : Fin n → ι → ℝ≥0) (j : Fin n), M.s (Function.update x j 0) j = 0)) ∧
    RevDS μ = ⨆ (M : MechanismN n ι) (_ : IsAdmissibleDS M ∧ IsNPTN M),
      (expRevenueN μ M).toENNReal := by
  classical
  -- `s^j(0, x^{-j}) ≤ 0` (IR at a zero report)
  have hzero_le : ∀ M : MechanismN n ι, IsAdmissibleDS M →
      ∀ x j, M.s (Function.update x j 0) j ≤ 0 := by
    intro M hM x j
    have h := hM.2.2.1 (Function.update x j 0) j
    simp [payoffN] at h
    linarith
  -- `s^j(x) ≥ s^j(0, x^{-j})` (IC of type `0` against reporting `x^j`)
  have hge_zero : ∀ M : MechanismN n ι, IsAdmissibleDS M →
      ∀ x j, M.s (Function.update x j 0) j ≤ M.s x j := by
    intro M hM x j
    have h := hM.2.1 (Function.update x j 0) j (x j)
    simp only [Function.update_idem, Function.update_eq_self, payoffN,
      Function.update_self, Pi.zero_apply, NNReal.coe_zero, mul_zero,
      Finset.sum_const_zero, zero_sub] at h
    linarith
  refine ⟨fun M hM => ⟨fun hN x j => le_antisymm (hzero_le M hM x j) (hN _ _), fun h x j => ?_⟩, ?_⟩
  · have := hge_zero M hM x j
    rw [h x j] at this
    exact this
  apply le_antisymm
  · refine iSup₂_le fun M hM => ?_
    -- the normalized mechanism `s'^j(x) = s^j(x) - s^j(0, x^{-j})`
    let M' : MechanismN n ι :=
      { q := M.q
        s := fun x j => M.s x j - M.s (Function.update x j 0) j }
    have hpay' : ∀ x j, payoffN M' x j = payoffN M x j + M.s (Function.update x j 0) j := by
      intro x j; simp only [payoffN, M']; ring
    have hadm' : IsAdmissibleDS M' ∧ IsNPTN M' := by
      refine ⟨⟨hM.1, ?_, ?_, ?_⟩, ?_⟩
      · intro x j x'
        have h := hM.2.1 x j x'
        rw [hpay']
        simp only [M', Function.update_idem] at h ⊢
        linarith
      · intro x j
        rw [hpay']
        have h := hM.2.1 x j 0
        have hq : 0 ≤ ∑ i, M.q (Function.update x j 0) j i * (x j i : ℝ) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hM.1.1 _ j i).1 (x j i).2
        linarith
      · intro j
        exact (hM.2.2.2 j).sub ((hM.2.2.2 j).comp measurable_update_left)
      · intro x j
        have := hge_zero M hM x j
        simp only [M']
        linarith
    have hrev : expRevenueN μ M ≤ expRevenueN μ M' := by
      have hS : ∀ x, sellerRevenue M x ≤ sellerRevenue M' x := by
        intro x
        simp only [sellerRevenue, M']
        exact Finset.sum_le_sum fun j _ => by linarith [hzero_le M hM x j]
      have hS0 : ∀ x, 0 ≤ sellerRevenue M' x := by
        intro x
        simp only [sellerRevenue, M']
        exact Finset.sum_nonneg fun j _ => by linarith [hge_zero M hM x j]
      unfold expRevenueN
      apply EReal.sub_le_sub
      · exact_mod_cast lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hS x)
      · have : ∫⁻ x, ENNReal.ofReal (-sellerRevenue M' x) ∂μ = 0 := by
          have : (fun x => ENNReal.ofReal (-sellerRevenue M' x)) = fun _ => 0 := by
            funext x; exact ENNReal.ofReal_of_nonpos (by linarith [hS0 x])
          rw [this, lintegral_zero]
        rw [this]
        exact EReal.coe_ennreal_nonneg _
    exact (EReal.toENNReal_le_toENNReal hrev).trans
      (le_iSup₂ (f := fun (M : MechanismN n ι) (_ : IsAdmissibleDS M ∧ IsNPTN M) =>
        (expRevenueN μ M).toENNReal) M' hadm')
  · exact iSup₂_le fun M hM => le_iSup₂ (f := fun (M : MechanismN n ι) (_ : IsAdmissibleDS M) =>
        (expRevenueN μ M).toENNReal) M hM.1
