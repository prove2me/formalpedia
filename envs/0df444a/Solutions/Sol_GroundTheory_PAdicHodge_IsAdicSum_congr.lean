-- Prove2me | solution 1 for GroundTheory.PAdicHodge.IsAdicSum.congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:38.779095+00:00
-- url     : https://prove2.me/submissions/7a6016c0-877e-4845-8bdc-b70b435a178c

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
theorem _root_.solution {a b : ℕ → R} {s : R} (hs : IsAdicSum I a s) (h : ∀ n, a n = b n) :
    IsAdicSum I b s := by
  have : a = b := funext h
  rwa [← this]
end IsAdicSum
end GroundTheory.PAdicHodge
