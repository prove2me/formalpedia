-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.theta_sq_law_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:25:00.483524+00:00
-- url     : https://prove2.me/submissions/8f75e6f5-0173-4811-b228-2b9637e91c32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Theorems.Thm_GlobalTheory_ThetaCharMult_sp_rel_transpose
import Theorems.Thm_GlobalTheory_ThetaCharMult_shift_algebra
import Theorems.Thm_GlobalTheory_ThetaCharMult_dvd_mulVec
import Theorems.Thm_GlobalTheory_ThetaCharMult_phase_dvd
import Theorems.Thm_GlobalTheory_ThetaCharMult_half_mulVec
import Theorems.Thm_GlobalTheory_ThetaCharMult_theta_zero_shift_sq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofIntVec_dot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_ofRealVec_halfVec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_isSymm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_A
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_theta_sq_red
import Theorems.Thm_ReciprocityTheory_PTheta_eC_add
import Theorems.Thm_ReciprocityTheory_PTheta_eC_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ThetaCharMult
variable {g : ℕ}
namespace GlobalTheory.ThetaCharMult
theorem _root_.solution : ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ), γ ∈ Matrix.symplecticGroup (Fin g) ℤ → (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) → ∀ (c : ℂ) (n n' : Fin g → ℤ), (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) → (∀ i, (2 : ℤ) ∣ (γ.toBlocks₁₁ᵀ *ᵥ n) i - n i) ∧ (∀ i, (2 : ℤ) ∣ (γ.toBlocks₂₂ᵀ *ᵥ n') i - n' i) → (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ, theta (halfVec n) (halfVec n') (zAct γ τ z) (spAct γ τ) ^ 2 = c * (jAut γ τ).det * eC (expArg γ τ z) * theta (halfVec n) (halfVec n') z τ ^ 2) := by
  intro g γ hγ h8 c n n' h0 ⟨hn, hn'⟩ τ hτ z
  have hB : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₁₂ᵀ i j := fun i j => (h8 j i).1
  have hC : ∀ i j, (8 : ℤ) ∣ γ.toBlocks₂₁ᵀ i j := fun i j => (h8 j i).2
  have hj := jAut_isUnit hγ hτ
  have hσ := spAct_isSymm hγ hτ.1 hj
  set m := γ.toBlocks₁₁ᵀ *ᵥ n + γ.toBlocks₂₁ᵀ *ᵥ n' with hm
  set m' := γ.toBlocks₁₂ᵀ *ᵥ n + γ.toBlocks₂₂ᵀ *ᵥ n' with hm'
  obtain ⟨k1, k2⟩ := shift_algebra (cMat γ).toBlocks₁₁ (cMat γ).toBlocks₁₂ (cMat γ).toBlocks₂₁
    (cMat γ).toBlocks₂₂ τ (spAct γ τ) (jAut γ τ)⁻¹ hτ.1 hσ (Matrix.nonsing_inv_mul _ hj)
    (Matrix.mul_nonsing_inv _ hj) rfl (sp_A hγ hτ.1 hj) (sp_rel_transpose hγ).2
    (ofRealVec (halfVec n)) (ofRealVec (halfVec n')) z (ofRealVec (halfVec m))
    (ofRealVec (halfVec m')) (half_mulVec _ _ n n') (half_mulVec _ _ n n')
  have h := h0 τ hτ (z + τ *ᵥ ofRealVec (halfVec m) + ofRealVec (halfVec m'))
  have hred : theta (halfVec m) (halfVec m') z τ ^ 2 = theta (halfVec n) (halfVec n') z τ ^ 2 := by
    rw [theta_sq_red m m', theta_sq_red n n']
    have e1 : (fun i => m i % 2) = fun i => n i % 2 := by
      funext i
      have a1 := hn i
      have a2 := dvd_mulVec hC n' i
      simp only [hm, Pi.add_apply]
      omega
    have e2 : (fun i => m' i % 2) = fun i => n' i % 2 := by
      funext i
      have a1 := hn' i
      have a2 := dvd_mulVec hB n i
      simp only [hm', Pi.add_apply]
      omega
    rw [e1, e2]
  obtain ⟨t, ht⟩ := phase_dvd hγ hB hC n n'
  have hph : ofRealVec (halfVec n) ⬝ᵥ ofRealVec (halfVec n') -
      ofRealVec (halfVec m) ⬝ᵥ ofRealVec (halfVec m') = ((2 * t : ℤ) : ℂ) := by
    have ht' : ((n ⬝ᵥ n' : ℤ) : ℂ) - ((m ⬝ᵥ m' : ℤ) : ℂ) = 8 * (t : ℂ) := by exact_mod_cast ht
    simp only [ofRealVec_halfVec, smul_dotProduct, dotProduct_smul, ofIntVec_dot, smul_eq_mul]
    push_cast
    linear_combination (1 / 4 : ℂ) * ht'
  rw [zAct, k1, theta_zero_shift_sq _ _ _ hσ, theta_zero_shift_sq _ _ _ hτ.1, hred, ← mul_assoc,
    mul_assoc (c * _), ← eC_add, expArg, k2, hph, eC_add, eC_add, eC_int, mul_one] at h
  have hne : ∀ x, eC x ≠ 0 := fun x => Complex.exp_ne_zero _
  refine mul_left_cancel₀ (hne _) (h.trans ?_)
  rw [expArg]
  ring
end GlobalTheory.ThetaCharMult
