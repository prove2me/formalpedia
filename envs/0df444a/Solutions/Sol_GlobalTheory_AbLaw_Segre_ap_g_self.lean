-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.ap_g_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:22.762956+00:00
-- url     : https://prove2.me/submissions/041ad12d-dbf3-40b8-952f-6f56444ffb77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Theorems.Thm_GlobalTheory_AbLaw_Segre_val_res
import Theorems.Thm_GlobalTheory_AbLaw_Segre_pre_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}
namespace GlobalTheory.AbLaw.Segre
theorem _root_.solution (hH : H.IsLB) (i : H.ι) {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U i)) :
    ap p h (H.g i i).val = 1 := by
  have h₁ := congrArg (fun u => ap p (pre_left p h) u.val) (hH.g_self i)
  simpa only [val_res, ap_rs, Units.val_one, map_one] using h₁
end GlobalTheory.AbLaw.Segre
