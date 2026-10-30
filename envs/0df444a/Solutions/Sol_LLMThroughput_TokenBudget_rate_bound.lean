-- Prove2me | solution 1 for LLMThroughput.TokenBudget.rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:27:20.242404+00:00
-- url     : https://prove2.me/submissions/205cfdcd-15da-4930-b409-131c030f2cb2

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

namespace LLMThroughput.TokenBudget

theorem rate_bound_nat (P : Params) (hP : P.Valid) (b : ℕ) (hb : b ≤ P.bmax) :
    b * P.t P.bmax ≤ P.bmax * P.t b := by
  obtain ⟨hb0, ⟨k, hk⟩, _, _⟩ := hP
  have hkmax : (P.bmax + P.b0 - 1) / P.b0 = k := by
    rw [hk]
    have : P.b0 * k + P.b0 - 1 = (P.b0 - 1) + P.b0 * k := by omega
    rw [this, Nat.add_mul_div_left _ _ (by omega)]
    rw [Nat.div_eq_of_lt (by omega)]; simp
  set j := (b + P.b0 - 1) / P.b0 with hj
  have hbj : b ≤ P.b0 * j := by
    have := Nat.lt_mul_div_succ (b + P.b0 - 1) (show 0 < P.b0 by omega)
    rw [← hj, Nat.mul_succ] at this
    generalize P.b0 * j = m at this ⊢
    omega
  have hjk : j ≤ k := by
    rw [hj, ← hkmax]
    exact Nat.div_le_div_right (by omega)
  unfold Params.t
  rw [hkmax, ← hj, hk]
  calc b * (P.c + P.a * k) ≤ (P.b0 * j) * (P.c + P.a * k) := Nat.mul_le_mul_right _ hbj
    _ = P.b0 * (j * P.c + P.a * j * k) := by ring
    _ ≤ P.b0 * (k * P.c + P.a * j * k) := by
        apply Nat.mul_le_mul_left; apply Nat.add_le_add_right; exact Nat.mul_le_mul_right _ hjk
    _ = P.b0 * k * (P.c + P.a * j) := by ring

end LLMThroughput.TokenBudget

open LLMThroughput.TokenBudget in
theorem solution (P : LLMThroughput.TokenBudget.Params) (hP : P.Valid) (b : ℕ) (hb1 : 1 ≤ b)
    (hb : b ≤ P.bmax) :
    (b : ℝ) / (P.t b : ℝ) ≤ (P.bmax : ℝ) / (P.t P.bmax : ℝ) := by
  have h := rate_bound_nat P hP b hb
  have ht : (1 : ℝ) ≤ (P.t P.bmax : ℝ) := by exact_mod_cast hP.2.2.2
  rcases Nat.eq_zero_or_pos (P.t b) with h0 | hpos
  · rw [h0]; simp; positivity
  · rw [div_le_div_iff₀ (by exact_mod_cast hpos) (by linarith)]
    exact_mod_cast h
