-- Prove2me | solution 1 for GlobalTheory.AbLaw.Segre.ap_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:08:21.656715+00:00
-- url     : https://prove2.me/submissions/99b3d125-6856-4f3e-8c0d-48ce584cbba0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
import Theorems.Thm_GlobalTheory_AbLaw_Segre_val_res
import Theorems.Thm_GlobalTheory_AbLaw_Segre_pre_right

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
theorem _root_.solution (hH : H.IsLB) (i j k : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j))
    (h₂ : W ≤ p ⁻¹ᵁ (H.U j ⊓ H.U k)) (h₃ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U k)) :
    ap p h₃ (H.g i k).val = ap p h₁ (H.g i j).val * ap p h₂ (H.g j k).val := by
  have e := congrArg (fun u => ap p (le_pre p h₁ (pre_right p h₂)) u.val) (hH.cocycle i j k)
  simp only [val_res, ap_rs, Units.val_mul, map_mul] at e
  exact e.symm
end GlobalTheory.AbLaw.Segre
