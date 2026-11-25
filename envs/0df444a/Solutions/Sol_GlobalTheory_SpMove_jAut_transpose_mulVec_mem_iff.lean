-- Prove2me | solution 1 for GlobalTheory.SpMove.jAut_transpose_mulVec_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:20:39.650003+00:00
-- url     : https://prove2.me/submissions/5ca868b7-e999-4ed9-a28d-30b97e0bf1a7

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
import Theorems.Thm_GlobalTheory_SpMove_jAut_transpose_mulVec_period
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Key_Chi_jAut_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SpMove
open Matrix ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
namespace GlobalTheory.SpMove
theorem _root_.solution {g : ℕ} {δ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ}
    (hδ : δ ∈ Matrix.symplecticGroup (Fin g) ℤ) {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ SiegelH (Fin g)) (z : Fin g → ℂ) :
    (∃ m n : Fin g → ℤ, (jAut δ τ)ᵀ *ᵥ z = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) ↔
      ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + spAct δ τ *ᵥ (fun i => (n i : ℂ)) := by
  have hj := jAut_isUnit hδ hτ
  constructor
  · rintro ⟨m, n, h⟩
    have hu : IsUnit δᵀ := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact SymplecticGroup.symplectic_det hδ
    obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hu (Sum.elim n m)
    have h1 := jAut_transpose_mulVec_period hδ hτ w
    rw [hw] at h1
    refine ⟨fun i => w (Sum.inr i), fun i => w (Sum.inl i), ?_⟩
    have hinj : Function.Injective (jAut δ τ)ᵀ.mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]
      exact hj
    apply hinj
    rw [h, h1]
    rfl
  · rintro ⟨m, n, rfl⟩
    exact ⟨_, _, jAut_transpose_mulVec_period hδ hτ (Sum.elim n m)⟩
end GlobalTheory.SpMove
