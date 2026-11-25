-- Prove2me | solution 1 for GlobalTheory.ConstFam.secScal_iff_resF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:18:24.30909+00:00
-- url     : https://prove2.me/submissions/dd163292-2992-422f-9af1-2a3926ecc316

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Theorems.Thm_GlobalTheory_FieldBaseChange_secScal_iff
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_GC_fam__eq_3a137bedd551
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.ConstFam
theorem _root_.solution {j : ℕ} {α : D.X} (s₁ : SecFMod D F j α) (s : SecBMod D j α) (r : R) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε j) s₁ (D.famφB α) (DegPre.famε j) s (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ resF D F j α s = toF (R := R) F r • s₁ :=
  secScal_iff (isPullback_prB D F).w (GC.famφ_eq D F α) D.P.isLB s₁ s _ _
    ((Over.w (fst (TF (R := R) F) D.P.A)).symm.trans (congrArg _ (TF_hom F))) r
end GlobalTheory.ConstFam
