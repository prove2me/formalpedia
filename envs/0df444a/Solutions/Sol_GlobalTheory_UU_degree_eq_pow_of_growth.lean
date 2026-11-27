-- Prove2me | solution 1 for GlobalTheory.UU.degree_eq_pow_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:35:21.308558+00:00
-- url     : https://prove2.me/submissions/76ede998-234f-4b3f-b4a1-8228ee43fdc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LeOfPowLePolyMulPow
import Theorems.Thm_GlobalTheory_UU_le_of_pow_le_poly_mul_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UU
namespace GlobalTheory.UU
theorem _root_.solution :
    ∀ (h : ℕ → ℕ) (g c C a d q : ℕ), 1 ≤ c → 1 ≤ q → (∀ t t', t ≤ t' → h t ≤ h t') → (∀ t, 1 ≤ t → t ^ g ≤ c * h t ∧ h t ≤ C * t ^ g) → (∀ t, d * h t ≤ h (q * (t + a)) ∧ h (q * t) ≤ d * h (t + a)) → d = q ^ g := by
  intro h g c C a d q hc hq hm hg hd
  have h1 : 1 ≤ h 1 := by
    have := (hg 1 le_rfl).1
    rcases Nat.eq_zero_or_pos (h 1) with h0 | h0
    · simp [h0] at this
    · exact h0
  have up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e1 : q ^ (k + 1) * t = q ^ k * (q * t) := by ring
      rw [e1]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have e2 : t + (k + 1) * a = t + k * a + a := by ring
      rw [e2]
      refine le_trans (hm _ _ ?_) (hd (t + k * a)).2
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _
  have lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ, mul_comm]
      refine (Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))
      have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
      have e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)
  apply le_antisymm
  · apply le_of_pow_le_poly_mul_pow d (q ^ g) C a g
    intro k
    have hp : 1 ≤ q ^ k * (1 + k * a) := Nat.mul_pos (Nat.pow_pos hq) (by omega)
    refine (lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]; ring
  · apply le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have a1 := (hg _ hp).1
    have a2 := up k 1
    rw [mul_one] at a2
    have a3 := (hg (1 + k * a) (by omega)).2
    calc (q ^ g) ^ k = (q ^ k) ^ g := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ c * h (q ^ k) := a1
      _ ≤ c * (d ^ k * (C * (1 + k * a) ^ g)) :=
        Nat.mul_le_mul_left _ (a2.trans (Nat.mul_le_mul_left _ a3))
      _ = _ := by ring
end GlobalTheory.UU
