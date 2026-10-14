-- Prove2me | solution 1 for IntMul.HvdH.eval_cyclic_conv
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T21:11:16.688562+00:00
-- url     : https://prove2.me/submissions/da434e19-250a-4950-b0ef-4b5bc7233d63

import Mathlib

open Finset

namespace IntMul.HvdH.Twist

/-- Evaluation at an `r`-th root of unity turns cyclic convolution into multiplication. -/
theorem eval_cyclic_conv {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (x : A) (hx : x ^ r = 1)
    (u v : ZMod r → A) :
    (∑ j, u j * x ^ j.val) * (∑ j, v j * x ^ j.val) = ∑ j, (∑ k, u k * v (j - k)) * x ^ j.val := by
  have hpow : ∀ a b : ZMod r, x ^ (a + b).val = x ^ a.val * x ^ b.val := by
    intro a b
    rw [ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) r, pow_add, pow_mul, hx, one_pow, one_mul]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun l => ?_)
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, hpow]
  ring

/-- **Twisting turns cyclic convolution into negacyclic convolution** (the ring isomorphism
`S : (ℂ^r, ∗) → ℂ[y]/(y^r + 1)`, `x ↦ ζ y`, of Harvey–van der Hoeven §3.2, in coefficients). -/
theorem twist_negacyclic {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (ζ : A) (hζ : ζ ^ r = -1)
    (u v : ZMod r → A) (j : ZMod r) :
    ∑ k, (ζ ^ k.val * u k) * (ζ ^ (j - k).val * v (j - k)) * (if k.val ≤ j.val then 1 else -1) =
      ζ ^ j.val * ∑ k, u k * v (j - k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hk := ZMod.val_lt k
  have hj := ZMod.val_lt j
  split_ifs with h
  · have e : (j - k).val = j.val - k.val := by
      rw [show j - k = ((j.val - k.val : ℕ) : ZMod r) by
        rw [Nat.cast_sub h]; simp]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have : ζ ^ k.val * ζ ^ (j - k).val = ζ ^ j.val := by
      rw [e, ← pow_add, Nat.add_sub_cancel' h]
    linear_combination (u k * v (j - k)) * this
  · push Not at h
    have e : (j - k).val = j.val + r - k.val := by
      rw [show j - k = ((j.val + r - k.val : ℕ) : ZMod r) by
        rw [Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]; simp]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have : ζ ^ k.val * ζ ^ (j - k).val = -ζ ^ j.val := by
      rw [e, ← pow_add, show k.val + (j.val + r - k.val) = j.val + r by omega, pow_add, hζ]
      ring
    linear_combination (-(u k * v (j - k))) * this

/-- Multiplication in `A[y]/(y^r + 1)` on coefficient vectors is negacyclic convolution: for any
`z` with `z^r = -1`. -/
theorem eval_negacyclic {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (z : A) (hz : z ^ r = -1)
    (a b : ZMod r → A) :
    (∑ j, a j * z ^ j.val) * (∑ j, b j * z ^ j.val) =
      ∑ j, (∑ k, a k * b (j - k) * (if k.val ≤ j.val then 1 else -1)) * z ^ j.val := by
  have hpow : ∀ k l : ZMod r, z ^ k.val * z ^ l.val =
      z ^ (k + l).val * (if k.val ≤ (k + l).val then 1 else -1) := by
    intro k l
    have hk := ZMod.val_lt k
    have hl := ZMod.val_lt l
    rw [← pow_add, ZMod.val_add]
    rcases lt_or_ge (k.val + l.val) r with h | h
    · rw [Nat.mod_eq_of_lt h, if_pos (by omega), mul_one]
    · have hm : (k.val + l.val) % r = k.val + l.val - r := by
        rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
      rw [hm, if_neg (by omega)]
      conv_lhs => rw [show k.val + l.val = (k.val + l.val - r) + r by omega, pow_add, hz]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun l => ?_)
  simp only [Equiv.coe_addLeft, add_sub_cancel_left]
  rw [show a k * z ^ k.val * (b l * z ^ l.val) = a k * b l * (z ^ k.val * z ^ l.val) by ring,
    hpow k l]
  by_cases h : k.val ≤ (k + l).val <;> simp [h]

end IntMul.HvdH.Twist

theorem solution {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (x : A) (hx : x ^ r = 1)
    (u v : ZMod r → A) :
    (∑ j, u j * x ^ j.val) * (∑ j, v j * x ^ j.val) = ∑ j, (∑ k, u k * v (j - k)) * x ^ j.val :=
  IntMul.HvdH.Twist.eval_cyclic_conv r x hx u v
