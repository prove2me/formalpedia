-- Prove2me | solution 1 for GlobalTheory.SpMove.jAut_transpose_mulVec_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:03:21.732779+00:00
-- url     : https://prove2.me/submissions/1b9025ca-9702-42ff-a80f-94954fb77b64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolUnifReparam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_EntireEqZeroOrEqZeroOfMulEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ThetaLawSymplecticNormalForm
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_nAut_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_spAct_isSymm
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SpMove
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.SpMove
theorem _root_.solution {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (w : Fin g ⊕ Fin g → ℤ) :
    (jAut δ τ)ᵀ *ᵥ ((fun i => (w (Sum.inr i) : ℂ)) + spAct δ τ *ᵥ (fun i => (w (Sum.inl i) : ℂ))) =
      (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) + τ *ᵥ (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  have hs := spAct_isSymm hδ hτ.1 hj
  have h1 : (jAut δ τ)ᵀ * spAct δ τ = (nAut δ τ)ᵀ := by
    rw [← hs.eq, ← Matrix.transpose_mul, spAct_eq, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hj,
      Matrix.mul_one]
  have h2 : (fun i => ((δᵀ *ᵥ w) (Sum.inr i) : ℂ)) =
      (cMat δ).toBlocks₁₂ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₂ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Fintype.sum_sum_type]
  have h3 : (fun i => ((δᵀ *ᵥ w) (Sum.inl i) : ℂ)) =
      (cMat δ).toBlocks₁₁ᵀ *ᵥ (fun i => (w (Sum.inl i) : ℂ)) +
        (cMat δ).toBlocks₂₁ᵀ *ᵥ (fun i => (w (Sum.inr i) : ℂ)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, cMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Fintype.sum_sum_type]
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, h2, h3, jAut_eq, nAut_eq]
  simp only [Matrix.transpose_add, Matrix.transpose_mul, hτ.1.eq, Matrix.add_mulVec, Matrix.mulVec_add,
    Matrix.mulVec_mulVec]
  abel
end GlobalTheory.SpMove
