-- Prove2me | solution 1 for GlobalTheory.CompletePoint.fn_eq_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:00.223432+00:00
-- url     : https://prove2.me/submissions/628393e8-c346-40f4-b7a3-14aa367baaec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_iso_appTop
import Theorems.Thm_GlobalTheory_CompletePoint_iso_injective

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
variable {R : Type} [CommRing R] (I : Ideal R)
namespace GlobalTheory.CompletePoint
theorem _root_.solution [IsHausdorff I R] {a b : Γ(Spec (CommRingCat.of R), ⊤)}
    (h : ∀ e, (thick R I e).appTop.hom a = (thick R I e).appTop.hom b) : a = b := by
  apply iso_injective R
  refine IsHausdorff.eq_iff_smodEq (I := I) |>.2 fun n => ?_
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (n + 1)))).hom.hom (h n)
  rw [iso_appTop, iso_appTop, Ideal.Quotient.eq] at this
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  exact Ideal.pow_le_pow_right n.le_succ this
end GlobalTheory.CompletePoint
