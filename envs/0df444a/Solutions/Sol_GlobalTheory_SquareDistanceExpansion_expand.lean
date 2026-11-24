-- Prove2me | solution 1 for GlobalTheory.SquareDistanceExpansion.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:08.635158+00:00
-- url     : https://prove2.me/submissions/e78cd1d5-4a78-4dc3-81f6-c4f201731710

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
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (X Y X' Y' : Matrix (Fin n) (Fin n) R) :
    (1 + X + Y) * (1 + X' + Y') = 1 + X + Y + X' + Y' + X * X' + X * Y' + Y * X' + Y * Y' := by
  noncomm_ring
end GlobalTheory.SquareDistanceExpansion
