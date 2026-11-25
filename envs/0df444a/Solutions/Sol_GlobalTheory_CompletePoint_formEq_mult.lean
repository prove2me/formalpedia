-- Prove2me | solution 1 for GlobalTheory.CompletePoint.formEq_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:26:53.686016+00:00
-- url     : https://prove2.me/submissions/34cb6261-b1fa-458f-b769-525eb8a5515c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_P2M_GlobalTheory_CompletePoint_prod_gt_T_c59e414e56f6
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cPoint_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_prod_cub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CompletePoint
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
namespace GlobalTheory.CompletePoint
theorem _root_.solution {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (χ χ' : D.X) :
    FormEq (Sum.elim (DegPre.gtφT D T b (χ + χ')) fun k =>
        (lift (DegPre.cT D T χ) (lift (DegPre.cT D T χ') b)).left ≫ thφ D.P.A (x3 D.P.A) k)
      (Sum.elim DegPre.gtε thε) (Sum.elim (DegPre.gtφT D T b χ) (DegPre.gtφT D T b χ'))
      (Sum.elim DegPre.gtε DegPre.gtε) := by
  intro U _ h
  refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_gtφT b _ h)
    (prod_cub (DegPre.cT D T χ) (DegPre.cT D T χ') b h))).trans (Eq.trans ?_
    ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_gtφT b χ h) (prod_gtφT b χ' h))).symm)
  have : DegPre.cT D T (χ + χ') = DegPre.cT D T χ * DegPre.cT D T χ' := DVR.cPoint_add D T χ χ'
  rw [this]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.CompletePoint
