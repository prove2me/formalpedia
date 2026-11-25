-- Prove2me | solution 1 for GlobalTheory.EndCalc.act_isTor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:15:57.900747+00:00
-- url     : https://prove2.me/submissions/2d2d6f14-6031-48cb-bd3e-48357882add3

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
import Theorems.Thm_GlobalTheory_EndCalc_cmp_one
import Theorems.Thm_GlobalTheory_EndCalc_act_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
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
variable {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.EndCalc
theorem _root_.solution {E : EndU U} {t : Multiplicative D.toPre.X →* Fˣ} {g g' : GtPtF D.toPre F} (ht : IsTor t g)
    (h : E.Act g g') : IsTor (t.comp (AddMonoidHom.toMultiplicative E.h)) g' := by
  have := E.homB
  refine ⟨by rw [h.1, ht.1, MonObj.one_comp], fun χ y J hJ => ?_⟩
  have e : val (E.u χ) g.b.left y J = 1 :=
    (congrArg (fun b : TF (R := R) F ⟶ D.toPre.P.A => val (E.u χ) b.left y J) ht.1).trans (cmp_one (E.u_norm χ) hJ)
  have e' := act_val h χ hJ
  rw [e, _root_.mul_one] at e'
  exact (congrArg Units.val e').trans (ht.2 (E.h χ) y J hJ)
end GlobalTheory.EndCalc
