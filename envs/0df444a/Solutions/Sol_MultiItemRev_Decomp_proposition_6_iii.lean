-- Prove2me | solution 1 for MultiItemRev.Decomp.proposition_6_iii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:45:54.645732+00:00
-- url     : https://prove2.me/submissions/33356ac0-7ac3-45f1-b624-8298a7f6d8dd

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open MultiItemRev.Decomp

theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] (μ : Measure (ι → ℝ≥0))
    [IsProbabilityMeasure μ] :
    Rev μ = ⨆ (M : Mechanism ι) (_ : IsAdmissible M ∧ IsNPT M), (expRevenue μ M).toENNReal := by
  apply le_antisymm
  · unfold Rev
    refine iSup₂_le fun M hM => ?_
    obtain ⟨hfeas, hIC, hIR, hmeas⟩ := hM
    let x0 : ι → ℝ≥0 := fun _ => 0
    let c : ℝ := M.s x0
    have hb0 : buyerPayoff M x0 = -c := by simp [buyerPayoff, x0, c]
    have hc0 : c ≤ 0 := by
      have := hIR x0
      rw [hb0] at this
      linarith
    have hcs : ∀ x, c ≤ M.s x := by
      intro x
      have h := hIC x0 x
      rw [hb0] at h
      have h0 : ∑ i, M.q x i * ((x0 i : ℝ≥0) : ℝ) = 0 := by simp [x0]
      rw [h0] at h
      linarith
    have hbd : ∀ x, -c ≤ buyerPayoff M x := by
      intro x
      have h := hIC x x0
      have hnn : 0 ≤ ∑ i, M.q x0 i * ((x i : ℝ≥0) : ℝ) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (hfeas x0 i).1 (NNReal.coe_nonneg _))
      have : M.s x0 = c := rfl
      linarith
    let M' : Mechanism ι := ⟨M.q, fun x => M.s x - c⟩
    have hbM' : ∀ x, buyerPayoff M' x = buyerPayoff M x + c := by
      intro x
      simp only [buyerPayoff, M']
      ring
    have hM' : IsAdmissible M' ∧ IsNPT M' := by
      refine ⟨⟨hfeas, ?_, ?_, ?_⟩, ?_⟩
      · intro x x'
        rw [hbM']
        have h := hIC x x'
        show ∑ i, M.q x' i * ((x i : ℝ≥0) : ℝ) - (M.s x' - c) ≤ _
        linarith
      · intro x
        rw [hbM']
        linarith [hbd x]
      · exact hmeas.sub_const c
      · intro x
        show 0 ≤ M.s x - c
        linarith [hcs x]
    refine le_trans ?_ (le_iSup₂_of_le M' hM' le_rfl)
    have h1 : (expRevenue μ M).toENNReal ≤ ∫⁻ x, ENNReal.ofReal (M.s x) ∂μ := by
      have : expRevenue μ M ≤ ((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) := by
        unfold expRevenue
        calc _ ≤ ((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal) - 0 :=
              EReal.sub_le_sub le_rfl (EReal.coe_ennreal_nonneg _)
          _ = _ := sub_zero _
      calc (expRevenue μ M).toENNReal
          ≤ (((∫⁻ x, ENNReal.ofReal (M.s x) ∂μ : ℝ≥0∞) : EReal)).toENNReal :=
            EReal.toENNReal_le_toENNReal this
        _ = _ := EReal.toENNReal_coe
    have hB' : ∫⁻ x, ENNReal.ofReal (-(M'.s x)) ∂μ = 0 := by
      have : ∀ x, ENNReal.ofReal (-(M'.s x)) = 0 := fun x =>
        ENNReal.ofReal_of_nonpos (by show -(M.s x - c) ≤ 0; linarith [hcs x])
      simp only [this, lintegral_zero]
    have h2 : (expRevenue μ M').toENNReal = ∫⁻ x, ENNReal.ofReal (M'.s x) ∂μ := by
      unfold expRevenue
      rw [hB']
      simp
    have h3 : ∫⁻ x, ENNReal.ofReal (M.s x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (M'.s x) ∂μ :=
      lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (by show M.s x ≤ M.s x - c; linarith))
    exact h1.trans (h3.trans h2.ge)
  · refine iSup₂_le fun M hM => ?_
    exact le_iSup₂_of_le M hM.1 le_rfl
