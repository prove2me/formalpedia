-- Prove2me | solution 1 for GroundTheory.GroupCoh.leftUnitor_tateCup_tateOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:00:02.117817+00:00
-- url     : https://prove2.me/submissions/6202e308-2a38-43cd-991b-c722dab9e48d

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateCupUnit
import Theorems.Thm_GroundTheory_GroupCoh_leftUnitor_tateCup_tateOne_zero
import Theorems.Thm_GroundTheory_GroupCoh_leftUnitor_tateCup_tateOne_down
import Theorems.Thm_GroundTheory_GroupCoh_leftUnitor_tateCup_tateOne_up

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
theorem _root_.solution (q : ℤ) (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by
  induction q using Int.induction_on generalizing B with
  | zero => exact leftUnitor_tateCup_tateOne_zero B b
  | succ i ih => exact leftUnitor_tateCup_tateOne_up (i : ℤ) _ rfl ih B b
  | pred i ih => exact leftUnitor_tateCup_tateOne_down _ (-(i : ℤ)) (by ring) ih B b
end GroundTheory.GroupCoh
