-- Prove2me | solution 1 for GroundTheory.GroupCoh.restrictEnd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:54.388997+00:00
-- url     : https://prove2.me/submissions/6bc3dfb2-2778-43e0-a7de-be6b59ef8dcf

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
namespace GroundTheory.GroupCoh
theorem _root_.solution (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) (x : S) :
    (restrictEnd f S hS x : B) = f x :=
  rfl
end GroundTheory.GroupCoh
