-- Prove2me | solution 1 for GroundTheory.Global.eq_zero_of_forall_infinitePlace_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:33.365032+00:00
-- url     : https://prove2.me/submissions/f066f70f-8ec3-4a60-9638-4fb2d518261d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]
variable [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (z : 𝓞 K) (h : ∀ w : InfinitePlace K, w z < 1) :
    z = 0 := by
  by_contra hz
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact (one_le_of_lt_one hz fun w' _ => h w').not_gt (h w)
end GroundTheory.Global
