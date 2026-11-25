-- Prove2me | solution 1 for GlobalTheory.ConstFam.IsFETranslate.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:38:14.649312+00:00
-- url     : https://prove2.me/submissions/270e4b12-ca45-42fe-b755-297bc37915d6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ThetaGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsFETranslateFeTranslate
import Theorems.Thm_GlobalTheory_ConstFam_resF_injective
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_sec_ext__7d36e2669680
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_fe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_secRel_iff


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
namespace IsFETranslate
theorem _root_.solution (hG : GlobalFnsSt) {j : ℕ} {mu α : D.X} {s : SecBMod D j α}
    {t t' : SecBMod D j (α + j • mu)} (h : IsFETranslate D j mu α s t) (h' : IsFETranslate D j mu α s t') : t = t' := by
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := FractionRing R) hG j mu α
  refine resF_injective D (FractionRing R) j _ (sec_ext' D.P.isLB fun y J hJ => ?_)
  exact ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h u hu hc) _ _ y J hJ).trans
    ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h' u hu hc) _ _ y J hJ).symm
end IsFETranslate
end GlobalTheory.ConstFam
