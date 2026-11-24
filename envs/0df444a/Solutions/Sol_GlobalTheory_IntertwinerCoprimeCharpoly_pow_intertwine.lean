-- Prove2me | solution 1 for GlobalTheory.IntertwinerCoprimeCharpoly.pow_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:52:09.33185+00:00
-- url     : https://prove2.me/submissions/8ace9b08-6ea4-40a2-bce6-06c9599d1514

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfIntertwineOfIsCoprimeCharpoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwinerCoprimeCharpoly
open Polynomial
namespace GlobalTheory.IntertwinerCoprimeCharpoly
theorem _root_.solution {K : Type} [Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K) (h : C * A = B * C) (n : ℕ) :
    C * A ^ n = B ^ n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc]
end GlobalTheory.IntertwinerCoprimeCharpoly
