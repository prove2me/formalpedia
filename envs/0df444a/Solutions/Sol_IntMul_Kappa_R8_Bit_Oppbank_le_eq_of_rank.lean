-- Prove2me | solution 1 for IntMul.Kappa.R8.Bit.Oppbank.le_eq_of_rank
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T19:12:32.511878+00:00
-- url     : https://prove2.me/submissions/3acf9b5e-ff58-4448-9dd7-0db4069f1c71

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R6_Defs20
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open NetLabels
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank

private theorem rank_idem {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (h : P * P = P) :
    (P.rank : ℚ) = P.trace :=
  NetLabels.rank_eq_trace_of_idem P h

private theorem le_rank {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ}
    (hA : A * A = A) (hB : B * B = B) (h : Le A B) :
    A.rank ≤ B.rank ∧ (B - A).rank = B.rank - A.rank := by
  have hD := le_sub_idem hA hB h
  have e := rank_idem hD
  rw [Matrix.trace_sub, ← rank_idem hA, ← rank_idem hB] at e
  have hle : A.rank ≤ B.rank := by
    have : (0 : ℚ) ≤ (B.rank : ℚ) - A.rank := by rw [← e]; positivity
    exact_mod_cast (sub_nonneg.1 this)
  refine ⟨hle, ?_⟩
  have : ((B - A).rank : ℚ) = ((B.rank - A.rank : ℕ) : ℚ) := by rw [e, Nat.cast_sub hle]
  exact_mod_cast this

theorem solution {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℚ}
    (hA : A * A = A) (hB : B * B = B) (h : Le A B) (hr : B.rank ≤ A.rank) : B = A := by
  have h0 : (B - A).rank = 0 := by rw [(le_rank hA hB h).2]; omega
  have h1 : LinearMap.range (B - A).mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
  have h2 : (B - A).mulVecLin = 0 := LinearMap.range_eq_bot.1 h1
  have : B - A = 0 := by
    ext i j
    have := congrArg (fun f => f (Pi.single j 1) i) h2
    simpa [Matrix.mulVec_single] using this
  exact sub_eq_zero.1 this
