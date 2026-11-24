-- Prove2me | solution 1 for HermitekLEAN.leading_term_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:12.01717+00:00
-- url     : https://prove2.me/submissions/6b263f5e-11ae-42e5-8f0d-e1391f0917d6

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_ModulusRigidity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset
open scoped Topology
noncomputable section
open HermitekLEAN
namespace HermitekLEAN
theorem _root_.solution :
    ∀ {N : ℕ} {α : ℂ} {q : ℝ → ℂ},
      (∀ ε : ℝ, 0 < ε → ∃ R0 : ℝ, ∀ r ≥ R0, ‖q r / (r ^ N : ℂ)‖ ≤ ε) →
        (∃ R0 : ℝ, ∀ r ≥ R0, α * (r ^ N : ℂ) + q r = 0) →
          α = 0 := by
  intro N α q hq hzero
  by_contra hα
  have hαnorm : 0 < ‖α‖ := norm_pos_iff.mpr hα
  obtain ⟨R1, hR1⟩ := hq (‖α‖ / 2) (by positivity)
  obtain ⟨R2, hR2⟩ := hzero
  let r : ℝ := max 1 (max R1 R2) + 1
  have hr1 : R1 ≤ r := by
    dsimp [r]
    linarith only [le_max_left R1 R2, le_max_right 1 (max R1 R2)]
  have hr2 : R2 ≤ r := by
    dsimp [r]
    linarith only [le_max_right R1 R2, le_max_right 1 (max R1 R2)]
  have hr_pos : 0 < r := by
    dsimp [r]
    linarith only [le_max_left 1 (max R1 R2)]
  have hsmall := hR1 r hr1
  have hzero_r := hR2 r hr2
  have hr_ne : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr_pos)
  have hpow : (r ^ N : ℂ) ≠ 0 := pow_ne_zero N hr_ne
  have hdiv : q r / (r ^ N : ℂ) = -α := by
    have hqeq : q r = -(α * (r ^ N : ℂ)) := by
      rw [eq_neg_iff_add_eq_zero]
      simpa [add_comm] using hzero_r
    rw [hqeq]
    field_simp [hpow]
  rw [hdiv, norm_neg] at hsmall
  linarith only [hαnorm, hsmall]
end HermitekLEAN
