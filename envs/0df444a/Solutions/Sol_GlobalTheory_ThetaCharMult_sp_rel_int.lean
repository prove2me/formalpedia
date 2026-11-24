-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.sp_rel_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:29:42.001766+00:00
-- url     : https://prove2.me/submissions/76c81ec9-dabf-4fa2-84b0-16b1c35f6242

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Theorems.Thm_GlobalTheory_ThetaCharMult_sp_rel_transpose

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
theorem _root_.solution {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hγ : γ ∈ Matrix.symplecticGroup (Fin g) ℤ) :
    γ.toBlocks₁₁ * γ.toBlocks₂₂ᵀ = 1 + γ.toBlocks₁₂ * γ.toBlocks₂₁ᵀ := by
  have h := (sp_rel_transpose hγ).1
  have h' : (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ =
      1 + (cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ := by
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  ext i j
  have := congrFun (congrFun h' i) j
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply, cMat, Matrix.toBlocks₁₁,
    Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.map_apply] at this ⊢
  exact_mod_cast this
end GlobalTheory.ThetaCharMult
