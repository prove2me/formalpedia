-- Prove2me | solution 1 for GlobalTheory.ThetaCharMult.sp_rel_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:52.433857+00:00
-- url     : https://prove2.me/submissions/ccc8df58-113c-4f9d-bf02-e4b28b9c49a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaSqLawOfZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_sp_rel


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
    ((cMat γ).toBlocks₁₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₁₁ * (cMat γ).toBlocks₂₂ᵀ = -1) ∧
    ((cMat γ).toBlocks₂₂ * (cMat γ).toBlocks₂₁ᵀ - (cMat γ).toBlocks₂₁ * (cMat γ).toBlocks₂₂ᵀ = 0) := by
  obtain ⟨-, r2, -, r4⟩ := sp_rel (SymplecticGroup.transpose_mem hγ)
  exact ⟨r2, r4⟩
end GlobalTheory.ThetaCharMult
