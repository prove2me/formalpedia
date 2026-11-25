-- Prove2me | solution 1 for GlobalTheory.InvFieldBasis.evalPt_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:35:22.117712+00:00
-- url     : https://prove2.me/submissions/e4849b99-6cd5-492a-b0f9-fbbd056810dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PreimageTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsIsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivations
import Theorems.Thm_GlobalTheory_InvFieldBasis_evalPt_pbT
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
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
open GlobalTheory.KS GlobalTheory.TangentOrigin GlobalTheory.SqZero GlobalTheory.LieBaseChange
open ReciprocityTheory.ChartRestriction.G.Chart (sp fstD pushR pullR fB)
open TrivSqZeroExt (inl inr)
noncomputable section
open GlobalTheory GlobalTheory.InvFieldBasis
variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {n : ℕ}
variable {C : Type} [CommRing C] [Algebra K C] {B : Type} [CommRing B] [Algebra K B]
namespace GlobalTheory.InvFieldBasis
theorem _root_.solution {Y Z : Scheme.{0}} (x : Sp B ⟶ Z) (f : Z ⟶ Y) (O : Y.Opens) (y : Sp B ⟶ Y) (hy : x ≫ f = y)
    (h' : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ O)) (h'' : ⊤ ≤ y ⁻¹ᵁ O) (s : Γ(Y, O)) :
    evalPt y O h'' s = evalPt x _ h' ((f.app O).hom s) := by
  rw [← evalPt_pbT x f (le_refl (f ⁻¹ᵁ O)) h' y hy h'' s]
  congr 1
  simp [pbT, Scheme.Hom.app_eq_appLE]
end GlobalTheory.InvFieldBasis
