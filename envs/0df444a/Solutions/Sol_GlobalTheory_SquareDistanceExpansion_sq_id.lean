-- Prove2me | solution 1 for GlobalTheory.SquareDistanceExpansion.sq_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:11.084174+00:00
-- url     : https://prove2.me/submissions/ef3cea4e-b469-4f56-a877-35846c32ca54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SqId

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SquareDistanceExpansion
open Matrix
namespace GlobalTheory.SquareDistanceExpansion
theorem _root_.solution {R : Type} [CommRing R] {d : ℕ} (H H' : Matrix (Fin d) (Fin d) R) :
    H * H' - 1 = (H - 1) + (H' - 1) + (H - 1) * (H' - 1) := by
  noncomm_ring
end GlobalTheory.SquareDistanceExpansion
