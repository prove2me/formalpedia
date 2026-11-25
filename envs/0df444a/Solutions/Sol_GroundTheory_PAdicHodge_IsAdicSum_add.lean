-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsAdicSum.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:23.693379+00:00
-- url     : https://prove2.me/submissions/c9b80024-4390-40b3-8d6a-51d16be3b87e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_FactorizationFactorialLe
import Definitions.Def_GroundTheory_PAdicHodge_ACrisLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open _root_.WittVector
variable {R : Type*} [CommRing R] (I : Ideal R)
variable {I}
namespace GroundTheory.PAdicHodge
namespace IsAdicSum
theorem _root_.solution {a b : ℕ → R} {s t : R} (hs : IsAdicSum I a s) (ht : IsAdicSum I b t) :
    IsAdicSum I (fun n => a n + b n) (s + t) := fun k => by
  obtain ⟨N, hN⟩ := hs k
  obtain ⟨N', hN'⟩ := ht k
  refine ⟨max N N', fun M hM => ?_⟩
  have := add_mem (hN M (le_of_max_le_left hM)) (hN' M (le_of_max_le_right hM))
  rw [Finset.sum_add_distrib]
  convert this using 1
  ring
end IsAdicSum
end GroundTheory.PAdicHodge
