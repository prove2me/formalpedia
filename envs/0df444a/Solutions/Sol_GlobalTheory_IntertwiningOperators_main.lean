-- Prove2me | solution 1 for GlobalTheory.IntertwiningOperators.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:08:40.252994+00:00
-- url     : https://prove2.me/submissions/6b99d250-f75c-4328-8960-73b48f8f98a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerBis
import Theorems.Thm_GlobalTheory_IntertwiningOperators_intertwine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntertwiningOperators
open Polynomial
namespace GlobalTheory.IntertwiningOperators
theorem _root_.solution : ∀ {K : Type} [inst : Field K] {a b : ℕ} (A : Matrix (Fin a) (Fin a) K)
    (B : Matrix (Fin b) (Fin b) K) (C : Matrix (Fin b) (Fin a) K),
    IsCoprime (Matrix.charpoly A) (Matrix.charpoly B) → C * A = B * C →
      C = (0 : Matrix (Fin b) (Fin a) K) := by
  intro K _ a b A B C hcop h
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval B u * aeval B (Matrix.charpoly A) = 1 := by
    have := congrArg (aeval B) huv
    rw [map_add, map_mul, map_mul, Matrix.aeval_self_charpoly, mul_zero, add_zero, map_one] at this
    exact this
  have h2 : aeval B (Matrix.charpoly A) * C = 0 := by
    rw [intertwine A B C h, Matrix.aeval_self_charpoly, Matrix.mul_zero]
  calc C = (aeval B u * aeval B (Matrix.charpoly A)) * C := by rw [h1, Matrix.one_mul]
    _ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
end GlobalTheory.IntertwiningOperators
