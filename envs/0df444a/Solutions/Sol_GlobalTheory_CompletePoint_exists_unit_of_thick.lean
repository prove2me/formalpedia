-- Prove2me | solution 1 for GlobalTheory.CompletePoint.exists_unit_of_thick
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:45:02.163556+00:00
-- url     : https://prove2.me/submissions/60094c95-e8d2-41a4-9131-322b745b1ca6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueTorusExtensionPointOfGroupPoint
import Theorems.Thm_GlobalTheory_CompletePoint_fn_eq_of_thick
import Theorems.Thm_GlobalTheory_CompletePoint_exists_fn_of_thick

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
theorem _root_.solution [IsAdicComplete I R] (a : ∀ e, Γ(Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e, pullU (thickTrans R I e) ⊤ (a (e + 1)) = a e) :
    ∃ b : Γ(Spec (CommRingCat.of R), ⊤)ˣ, ∀ e, pullU (thick R I e) ⊤ b = a e := by
  obtain ⟨b, hb⟩ := exists_fn_of_thick I (fun e => (a e).val) fun e => congrArg Units.val (h e)
  obtain ⟨c, hc⟩ := exists_fn_of_thick I (fun e => (a e)⁻¹.val) fun e =>
    congrArg Units.val ((map_inv _ _).trans (congrArg (·⁻¹) (h e)))
  have hbc : b * c = 1 := fn_eq_of_thick I fun e => by
    rw [map_mul, hb, hc, map_one]; exact (a e).mul_inv
  exact ⟨⟨b, c, hbc, (mul_comm _ _).trans hbc⟩, fun e => Units.ext (hb e)⟩
end GlobalTheory.CompletePoint
