-- Prove2me | solution 1 for GlobalTheory.SquareDistanceExpansion.dist
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:57:07.809172+00:00
-- url     : https://prove2.me/submissions/a1098383-d309-40fe-8dc6-8e337da315cc

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
theorem _root_.solution {R : Type} [CommRing R] {n d : ℕ} (a : Matrix (Fin n) (Fin d) R)
    (α : Matrix (Fin d) (Fin n) R) (A B : Matrix (Fin d) (Fin d) R) :
    a * (A + B + A * B) * α = a * A * α + a * B * α + a * A * B * α := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
end GlobalTheory.SquareDistanceExpansion
