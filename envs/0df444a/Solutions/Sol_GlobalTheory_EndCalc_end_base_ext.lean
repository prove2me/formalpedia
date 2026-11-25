-- Prove2me | solution 1 for GlobalTheory.EndCalc.end_base_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:29:22.836816+00:00
-- url     : https://prove2.me/submissions/72b1c2c6-f681-441c-b517-70c3bd51b5ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
import Theorems.Thm_GlobalTheory_sec_eq_zero_and_hom_eq_of_thickenings
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
open GlobalTheory.TorusExt
variable {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {U : UnifPre I D A G}
namespace GlobalTheory.EndCalc
theorem _root_.solution (hR : AdmBase R I) (U : UnifPre I D A G) {b b' : D.toPre.P.A ⟶ D.toPre.P.A}
    (h : ∀ e, (U.gt e).q ≫ (Over.pullback (thick R I e)).map b = (U.gt e).q ≫ (Over.pullback (thick R I e)).map b') :
    b = b' := by
  obtain ⟨_, -, -, _⟩ := hR
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  have := D.toPre.P.isAb.proper
  refine (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I) D.toPre.P.A).2 _ b b' fun e => ?_
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  have := FlatQuotient.epi_of_flat_surjective (U.gt e).q
  have k := congrArg (fun q => q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) ((cancel_epi _).1 (h e))
  exact (pullback.lift_fst _ _ _).symm.trans (k.trans (pullback.lift_fst _ _ _))
end GlobalTheory.EndCalc
