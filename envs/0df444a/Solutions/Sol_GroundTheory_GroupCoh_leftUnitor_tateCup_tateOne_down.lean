-- Prove2me | solution 1 for GroundTheory.GroupCoh.leftUnitor_tateCup_tateOne_down
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:47:58.671793+00:00
-- url     : https://prove2.me/submissions/907a3f9b-49be-4d2c-8d19-0d7d806e5464

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateCupUnit
import Theorems.Thm_P2M_GroundTheory_GroupCoh___leftUnitor_apply_453fbefc83a9
import Theorems.Thm_GroundTheory_GroupCoh_augSES_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorLeft_shortExact
import Theorems.Thm_GroundTheory_GroupCoh_moduleIso_hom_injective
import Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_leftRegular_tensor
import Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCup___right_e29a4e04fc7a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (q q' : ℤ) (hq : q + 1 = q')
    (h : ∀ (B : Rep.{u} k G) (b : tateCohomology B q'),
      ((tateCohomologyFunctor q').map (λ_ B).hom).hom
        (tateCup 0 q' (𝟙_ (Rep.{u} k G)) B q' (zero_add _) (tateOne k G) b) = b)
    (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  subst hq
  have hE := augSES_shortExact B
  have hAE := augSES_tensorLeft_shortExact (𝟙_ (Rep.{u} k G)) B
  have hiso : IsIso (TateCohomology.δ hE q) :=
    isIso_δ_of_tateAcyclic hE (tateAcyclic_leftRegular_tensor B) q
  apply moduleIso_hom_injective (@asIso _ _ _ _ _ hiso)
  refine (δ_leftUnitor_apply hE hAE q _).trans ?_
  have hr := tateCup_δ_right hE (𝟙_ (Rep.{u} k G)) hAE 0 q q (zero_add q) (tateOne k G) b
  rw [Int.negOnePow_zero, one_smul] at hr
  refine (congrArg (((tateCohomologyFunctor (q + 1)).map (λ_ _).hom).hom) hr).trans ?_
  exact h _ _
end GroundTheory.GroupCoh
