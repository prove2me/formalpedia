-- Prove2me | solution 1 for GlobalTheory.KS.EndClass.pbT_pbT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:23:09.891067+00:00
-- url     : https://prove2.me/submissions/54411e42-200e-4ae6-8fd3-3b9024759c95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
namespace GlobalTheory.KS.EndClass
theorem _root_.solution (t : T ⟶ Z) (f : Z ⟶ Y) {O₀ : Y.Opens} {O₁ : Z.Opens} {O₂ : T.Opens} (h₁ : O₁ ≤ f ⁻¹ᵁ O₀)
    (h₂ : O₂ ≤ t ⁻¹ᵁ O₁) (s : Γ(Y, O₀)) : pbT t (pbT f s O₁) O₂ = pbT (t ≫ f) s O₂ := by
  have h₃ : O₂ ≤ (t ≫ f) ⁻¹ᵁ O₀ := h₂.trans (t.preimage_mono h₁)
  simp only [pbT, dif_pos h₁, dif_pos h₂, dif_pos h₃]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.KS.EndClass
