-- Prove2me | solution 1 for LanglandsTunnell.hermite_fourfold_reflection_eq_sum_filter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ad79f389-36a3-578f-a1a6-3815a204b08e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_hermite_fourfold_reflection_eq_sum_filter

set_option autoImplicit false

open Complex Finset

namespace BF9

theorem v0 : (0 : ZMod 2).val = 0 := rfl
theorem v1 : (1 : ZMod 2).val = 1 := rfl

theorem trinom (x y z : ℂ) (n : ℕ) :
    (x + y + z) ^ n = ∑ i ∈ range (n + 1), ∑ j ∈ range (n - i + 1),
      ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
        (x ^ i * y ^ j * z ^ (n - i - j)) := by
  rw [add_assoc, add_pow]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := by simp at hi; omega
  rw [add_pow, mul_sum, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n - i := by simp at hj; omega
  rw [Nat.cast_choose ℂ hi', Nat.cast_choose ℂ hj']
  have f1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have f2 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have f3 : ((n - i - j).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have f4 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

theorem trinom_box (x y z : ℂ) {n N : ℕ} (hn : n ≤ N) :
    (x + y + z) ^ n = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), ∑ l ∈ range (N + 1),
      if i + j + l = n then
        ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) * (x ^ i * y ^ j * z ^ l)
      else 0 := by
  rw [trinom]

  have step_i : ∀ i ∈ range (N + 1), (∑ j ∈ range (N + 1), ∑ l ∈ range (N + 1),
      if i + j + l = n then
        ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) * (x ^ i * y ^ j * z ^ l)
      else 0) =
      if i ≤ n then ∑ j ∈ range (n - i + 1),
        ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
          (x ^ i * y ^ j * z ^ (n - i - j)) else 0 := by
    intro i hi
    split_ifs with hin
    ·
      have inner : ∀ j ∈ range (N + 1), (∑ l ∈ range (N + 1),
          if i + j + l = n then
            ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) * (x ^ i * y ^ j * z ^ l)
          else 0) =
          if j ≤ n - i then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
            (x ^ i * y ^ j * z ^ (n - i - j)) else 0 := by
        intro j hj
        split_ifs with hjn
        · rw [← sum_filter]
          have : (range (N + 1)).filter (fun l => i + j + l = n) = {n - i - j} := by
            ext l; simp only [mem_filter, mem_range, mem_singleton]; omega
          rw [this, sum_singleton]
        · refine sum_eq_zero fun l hl => ?_
          rw [if_neg]; omega
      rw [sum_congr rfl inner, ← sum_filter]
      have : (range (N + 1)).filter (fun j => j ≤ n - i) = range (n - i + 1) := by
        ext j; simp only [mem_filter, mem_range]; omega
      rw [this]
    · refine sum_eq_zero fun j hj => sum_eq_zero fun l hl => ?_
      rw [if_neg]; omega
  rw [sum_congr rfl step_i, ← sum_filter]
  have : (range (N + 1)).filter (fun i => i ≤ n) = range (n + 1) := by
    ext i; simp only [mem_filter, mem_range]; omega
  rw [this]

theorem neg_one_pow_val_add (a b : ZMod 2) : (-1 : ℂ) ^ (a + b).val = (-1 : ℂ) ^ a.val * (-1 : ℂ) ^ b.val := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a with rfl | rfl <;>
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with rfl | rfl
  · rw [add_zero, v0]; simp
  · rw [zero_add, v0, v1]; simp
  · rw [add_zero, v0, v1]; simp
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, v0, v1]; norm_num

theorem bracket (a₃ c ē : ZMod 2) (m i j l r : ℕ) (h : i + j + l + 2 * r = m) :
    ((-1 : ℂ) ^ j * (-1) ^ l + (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * ((-1) ^ i * (-1) ^ j) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ c.val * (-1) ^ j +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * ((-1) ^ i * (-1) ^ j * (-1) ^ l)) =
    if ((j : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((l : ZMod 2) = ē + c) then
      4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + ē).val) else 0 := by
  have him : (-1 : ℂ) ^ i = (-1) ^ m * ((-1) ^ j * (-1) ^ l) := by
    have e1 : (-1 : ℂ) ^ m = (-1) ^ i * ((-1) ^ j * (-1) ^ l) := by
      rw [← h, pow_add, pow_add, pow_add, pow_mul]; norm_num; ring
    have sj : (-1 : ℂ) ^ j * (-1) ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    have sl : (-1 : ℂ) ^ l * (-1) ^ l = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [e1]
    linear_combination (-((-1 : ℂ) ^ i * (-1) ^ l * (-1) ^ l)) * sj + (-((-1 : ℂ) ^ i)) * sl
  rw [him, neg_one_pow_val_add, neg_one_pow_val_add]
  rcases Nat.even_or_odd m with hm | hm <;>
  rcases Nat.even_or_odd j with hj | hj <;>
  rcases Nat.even_or_odd l with hl | hl <;>
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a₃ with rfl | rfl <;>
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl <;>
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) ē with rfl | rfl <;>
  · simp only [hm.neg_one_pow, hj.neg_one_pow, hl.neg_one_pow, hm.natCast_zmod_two, hj.natCast_zmod_two,
      hl.natCast_zmod_two, v0, v1]
    split_ifs with hc <;>
      first
        | (exfalso; revert hc; decide)
        | norm_num
        | (norm_num at hc)

end BF9

open BF9 Finset in

theorem solution
    (m : ℕ) (a₃ c ē : ZMod 2) (u v w : ℂ) :
    (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (u - v - w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (-u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ c.val * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (-u - v - w) ^ (m - 2 * r)) =
      4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + ē).val) *
        ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = ē + c)),
          ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) /
              ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                (4 * (Real.pi : ℂ)) ^ T.1.1)) *
            u ^ T.1.2 * v ^ T.2.1 * w ^ T.2.2 := by

  set s4 : ℂ := 4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + ē).val) with hs4
  set K : ℕ → ℕ → ℕ → ℕ → ℂ := fun r i j l =>
    (-1 : ℂ) ^ r * (m.factorial : ℂ) /
      ((r.factorial : ℂ) * (i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) with hK
  set cR : ℕ → ℂ := fun r =>
    (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) with hcR
  have hπ : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

  have per_r : ∀ r ∈ range (m / 2 + 1),
      cR r * (u - v - w) ^ (m - 2 * r) +
        (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (cR r * (-u - v + w) ^ (m - 2 * r)) +
        (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ c.val * (cR r * (u - v + w) ^ (m - 2 * r)) +
        (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * (cR r * (-u - v - w) ^ (m - 2 * r)) =
      ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), ∑ l ∈ range (m + 1),
        if i + j + l + 2 * r = m ∧ (((j : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((l : ZMod 2) = ē + c)) then
          s4 * (K r i j l * u ^ i * v ^ j * w ^ l) else 0 := by
    intro r hr
    have hr' : 2 * r ≤ m := by
      simp only [mem_range] at hr
      omega
    have hn : m - 2 * r ≤ m := Nat.sub_le _ _
    rw [show u - v - w = u + -v + -w by ring, show -u - v + w = -u + -v + w by ring,
      show u - v + w = u + -v + w by ring, show -u - v - w = -u + -v + -w by ring,
      trinom_box u (-v) (-w) hn, trinom_box (-u) (-v) w hn, trinom_box u (-v) w hn, trinom_box (-u) (-v) (-w) hn]
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
    by_cases hijl : i + j + l = m - 2 * r
    · have hcond : i + j + l + 2 * r = m := by omega
      simp only [if_pos hijl, hcond, true_and]
      rw [neg_pow u, neg_pow v, neg_pow w]
      have hb := bracket a₃ c ē m i j l r hcond

      have hA : cR r * ((((m - 2 * r).factorial : ℕ) : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) =
          K r i j l := by
        simp only [hcR, hK]
        have f0 : (((m - 2 * r).factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        have f1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        have f2 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        have f3 : (l.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        have f4 : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        have f5 : (4 * (Real.pi : ℂ)) ^ r ≠ 0 := pow_ne_zero _ hπ
        field_simp
      split_ifs with hpar
      · rw [if_pos hpar] at hb
        rw [← hA]
        linear_combination (cR r * ((((m - 2 * r).factorial : ℕ) : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) *
          (u ^ i * v ^ j * w ^ l)) * hb
      · rw [if_neg hpar] at hb
        linear_combination (cR r * ((((m - 2 * r).factorial : ℕ) : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) *
          (u ^ i * v ^ j * w ^ l)) * hb
    · have hcond : ¬ (i + j + l + 2 * r = m ∧ (((j : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((l : ZMod 2) = ē + c))) := by
        intro hc; apply hijl; omega
      simp only [if_neg hijl, if_neg hcond]
      ring

  have hL : (∑ r ∈ range (m / 2 + 1), cR r * (u - v - w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (∑ r ∈ range (m / 2 + 1), cR r * (-u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ c.val * (∑ r ∈ range (m / 2 + 1), cR r * (u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * (∑ r ∈ range (m / 2 + 1), cR r * (-u - v - w) ^ (m - 2 * r)) =
      ∑ r ∈ range (m + 1), ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), ∑ l ∈ range (m + 1),
        if i + j + l + 2 * r = m ∧ (((j : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((l : ZMod 2) = ē + c)) then
          s4 * (K r i j l * u ^ i * v ^ j * w ^ l) else 0 := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib, sum_congr rfl per_r]

    refine sum_subset (fun x hx => mem_range.mpr (by have := mem_range.mp hx; omega)) fun r hr hr' => ?_
    refine sum_eq_zero fun i _ => sum_eq_zero fun j _ => sum_eq_zero fun l _ => ?_
    rw [if_neg]
    simp only [mem_range, not_lt] at hr hr'
    intro hc; omega

  have hR : (∑ T ∈ ((range (m + 1) ×ˢ range (m + 1)) ×ˢ (range (m + 1) ×ˢ range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = ē + c)),
          K T.1.1 T.1.2 T.2.1 T.2.2 * u ^ T.1.2 * v ^ T.2.1 * w ^ T.2.2) =
      ∑ r ∈ range (m + 1), ∑ i ∈ range (m + 1), ∑ j ∈ range (m + 1), ∑ l ∈ range (m + 1),
        if i + j + l + 2 * r = m ∧ (((j : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((l : ZMod 2) = ē + c)) then
          K r i j l * u ^ i * v ^ j * w ^ l else 0 := by
    rw [sum_filter, sum_product, sum_product]
    refine sum_congr rfl fun r _ => sum_congr rfl fun i _ => ?_
    rw [sum_product]

  show (∑ r ∈ range (m / 2 + 1), cR r * (u - v - w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (∑ r ∈ range (m / 2 + 1), cR r * (-u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ c.val * (∑ r ∈ range (m / 2 + 1), cR r * (u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * (∑ r ∈ range (m / 2 + 1), cR r * (-u - v - w) ^ (m - 2 * r)) =
    s4 * ∑ T ∈ ((range (m + 1) ×ˢ range (m + 1)) ×ˢ (range (m + 1) ×ˢ range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = ē + c)),
          K T.1.1 T.1.2 T.2.1 T.2.2 * u ^ T.1.2 * v ^ T.2.1 * w ^ T.2.2
  rw [hL, hR]
  simp only [mul_sum, mul_ite, mul_zero]

end S_LanglandsTunnell_hermite_fourfold_reflection_eq_sum_filter
end P2MW
export P2MW.S_LanglandsTunnell_hermite_fourfold_reflection_eq_sum_filter (solution)
