-- Prove2me | solution 1 for GlobalTheory.EndCalc.act_comp_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:05.841665+00:00
-- url     : https://prove2.me/submissions/d19eef53-f33f-4af5-b19e-ab2f2c3b4224

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
import Theorems.Thm_GlobalTheory_EndCalc_cmp_comp
import Theorems.Thm_GlobalTheory_EndCalc_act_val
import Theorems.Thm_GlobalTheory_AddLaw_Proportional_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
theorem _root_.solution (hG : GlobalFnsSt) {E E' E'' : EndU U} (hb : E''.aB = E.aB ≫ E'.aB) (hh : E''.h = E.h.comp E'.h)
    {g g₁ g₂ : GtPtF D.toPre F} (h₁ : E.Act g g₁) (h₂ : E'.Act g₁ g₂) : E''.Act g g₂ := by
  have := E.homB
  refine ⟨by rw [h₂.1, h₁.1, hb, Category.assoc], fun χ y J hJ => ?_⟩
  have hp : E''.h χ = E.h (E'.h χ) := by rw [hh, AddMonoidHom.comp_apply]
  have e₁ := cmp_comp hG (E.u_norm (E'.h χ)) (E'.u_norm χ) (E''.u_norm χ) hb hp hJ g.b
  rw [← h₁.1] at e₁
  change charVal g₂ χ y J = charVal g (E''.h χ) y J * val (E''.u χ) g.b.left y J
  rw [act_val h₂ χ hJ, act_val h₁ _ hJ, e₁, _root_.mul_assoc]
  exact congrArg (fun k => charVal g k y J * _) hp.symm
end GlobalTheory.EndCalc
