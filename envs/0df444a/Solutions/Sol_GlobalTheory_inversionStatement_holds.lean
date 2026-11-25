-- Prove2me | solution 1 for GlobalTheory.inversionStatement_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:40.969025+00:00
-- url     : https://prove2.me/submissions/4e7e874f-02b7-423b-9d44-276d3cf7c5c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_HasSumLocallyUniformlyOnIteratedFDerivRiemannThe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_GenMain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FromBlocksMapIntCastMemSymplecticGroup
import Theorems.Thm_GlobalTheory_IsSiegel_riemannTheta_char_eq_neg_inv
import Theorems.Thm_GlobalTheory_IsSiegel_siegelGaussIntegral_sq_mul_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped Real
noncomputable section
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
variable {g : ℕ} {γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
namespace GlobalTheory
theorem _root_.solution : InversionStatement := by
  intro g a b τ hτ z
  have hS : IsSiegel τ := ⟨hτ.1, hτ.2⟩
  have h1 : theta b (-a) z τ = siegelGaussIntegral τ * cexp (-(π * I) * (z ⬝ᵥ (τ⁻¹ *ᵥ z)) -
      2 * π * I * (ofRealVec a ⬝ᵥ ofRealVec b)) * theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) :=
    hS.riemannTheta_char_eq_neg_inv a b z
  have h2 := hS.siegelGaussIntegral_sq_mul_det
  rw [det_smul, Fintype.card_fin] at h2
  have h3 : eC (z ⬝ᵥ (τ⁻¹ *ᵥ z)) * eC (2 * (ofRealVec a ⬝ᵥ ofRealVec b)) *
      cexp (-(π * I) * (z ⬝ᵥ (τ⁻¹ *ᵥ z)) - 2 * π * I * (ofRealVec a ⬝ᵥ ofRealVec b)) ^ 2 = 1 := by
    rw [eC, eC, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]
    congr 1
    ring
  rw [h1]
  linear_combination (-theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) ^ 2) * h2 -
    theta a b (τ⁻¹ *ᵥ z) (-τ⁻¹) ^ 2 * (siegelGaussIntegral τ ^ 2 * ((-I) ^ g * τ.det)) * h3
end GlobalTheory
