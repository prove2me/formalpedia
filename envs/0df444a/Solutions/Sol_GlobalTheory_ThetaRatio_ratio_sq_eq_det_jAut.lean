-- Prove2me | solution 1 for GlobalTheory.ThetaRatio.ratio_sq_eq_det_jAut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:29.921802+00:00
-- url     : https://prove2.me/submissions/39fc8acc-f56a-4e65-a213-1875982a4973

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_TwoDvdMultiplierOfThetaZActEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_RatioSqEqDetJAut
import Theorems.Thm_GlobalTheory_ThetaRatio_thetaChar_ofRealVec
import Theorems.Thm_GlobalTheory_ThetaRatio_exists_eq_halfVec
import Theorems.Thm_GlobalTheory_ThetaCharMult_theta_sq_law_of_zero
import Theorems.Thm_GlobalTheory_entire_eq_zero_of_mul_continuous_eq_zero
import Theorems.Thm_GlobalTheory_halfChar_fixed_of_theta_transform_unit
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ThetaRatio
namespace GlobalTheory.ThetaRatio
theorem _root_.solution : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = 1 * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → ∀ (c₁ c₂ : Fin g → ℂ), (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) → (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) → ∀ τ ∈ SiegelH (Fin g), ∀ (ρ : (Fin g → ℂ) → ℂ) (κ : ℂ), Differentiable ℂ ρ → (∀ z, ρ z ≠ 0) → ρ 0 = 1 → κ ≠ 0 → (∀ z, thetaChar (spAct γ τ) c₁ c₂ (zAct γ τ z) * ρ z = κ * thetaChar τ c₁ c₂ z) → κ ^ 2 = (jAut γ τ).det := by
  intro g γ hγ h8 h0 c₁ c₂ h₁ h₂ τ hτ ρ κ hρ hρ0 hρ1 hκ h
  obtain ⟨n, rfl⟩ := exists_eq_halfVec h₁
  obtain ⟨n', rfl⟩ := exists_eq_halfVec h₂
  simp only [thetaChar_ofRealVec] at h
  have hfix := halfChar_fixed_of_theta_transform_unit g γ hγ h8 1 n n' one_ne_zero h0 τ hτ
    (fun z => κ / ρ z) (by simpa only [div_eq_mul_inv] using (hρ.fun_inv hρ0).const_mul κ) (fun z => div_ne_zero hκ (hρ0 z))
    (fun z => by rw [div_mul_eq_mul_div, ← h z, mul_div_cancel_right₀ _ (hρ0 z)])
  have hlaw := ThetaCharMult.theta_sq_law_of_zero g γ hγ h8 1 n n' h0 hfix τ hτ
  have hE : Differentiable ℂ fun z => eC (expArg γ τ z) := by
    simp only [eC, expArg, dotProduct, mulVec]
    fun_prop
  have hθ : (fun z => theta (halfVec n) (halfVec n') z τ ^ 2) ≠ 0 := fun hz =>
    theta_ne_zero hτ (halfVec n) (halfVec n')
      (funext fun z => pow_eq_zero_iff (two_ne_zero) |>.1 (congrFun hz z))
  have key := entire_eq_zero_of_mul_continuous_eq_zero
    (f := fun z => (jAut γ τ).det * eC (expArg γ τ z) * ρ z ^ 2 - κ ^ 2)
    (((hE.const_mul _).mul (hρ.pow 2)).sub_const _)
    ((differentiable_theta hτ (halfVec n) (halfVec n')).continuous.pow 2) hθ
    (fun z => by
      have h1 := hlaw z
      have h2 : (theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) * ρ z) ^ 2 =
          (κ * theta (halfVec n) (halfVec n') z τ) ^ 2 := by rw [h z]
      show _ * theta (halfVec n) (halfVec n') z τ ^ 2 = 0
      linear_combination h2 - ρ z ^ 2 * h1) 0
  have e0 : eC (expArg γ τ 0) = 1 := by simp [expArg, eC]
  simp only [e0, hρ1] at key
  linear_combination -key
end GlobalTheory.ThetaRatio
