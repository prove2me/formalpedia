-- Prove2me | solution 1 for GlobalTheory.matrix_pow_mul_eq_mul_pow_of_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:19:38.708106+00:00
-- url     : https://prove2.me/submissions/ffde1d56-0981-4691-ac05-f94809025bec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {m r : ℕ} (X : Matrix (Fin m) (Fin m) ℂ)
    (ε : Matrix (Fin m) (Fin r) ℂ) (β : Matrix (Fin r) (Fin r) ℂ) (h : X * ε = ε * β) (n : ℕ) :
    X ^ n * ε = ε * β ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]
end GlobalTheory
