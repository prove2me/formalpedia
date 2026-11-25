-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsAdicSum.mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:26.720911+00:00
-- url     : https://prove2.me/submissions/6e449d77-4375-4196-b010-bf553f4394d9

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
theorem _root_.solution {J : Ideal R} {k : ℕ} (hJ : I ^ k ≤ J) {a : ℕ → R} {s : R}
    (hs : IsAdicSum I a s) (ha : ∀ n, a n ∈ J) : s ∈ J := by
  obtain ⟨N, hN⟩ := hs k
  have := add_mem (hJ (hN N le_rfl)) (Ideal.sum_mem J (t := Finset.range N) fun n _ => ha n)
  rwa [sub_add_cancel] at this
end IsAdicSum
end GroundTheory.PAdicHodge
