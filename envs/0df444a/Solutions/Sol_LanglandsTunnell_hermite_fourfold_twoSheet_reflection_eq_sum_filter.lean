-- Prove2me | solution 1 for LanglandsTunnell.hermite_fourfold_twoSheet_reflection_eq_sum_filter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7b93534a-c911-5bf2-a2f3-81f248722837

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.MellinTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_hermite_fourfold_twoSheet_reflection_eq_sum_filter

set_option autoImplicit false

open Complex

set_option maxHeartbeats 4000000
namespace HFR

theorem add_add_pow (x y z : ℂ) (n : ℕ) :
    (x + y + z) ^ n = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n - i + 1),
      ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
        x ^ i * y ^ j * z ^ (n - i - j) := by
  have h1 : (x + y + z) ^ n = ∑ i ∈ Finset.range (n + 1), x ^ i * (y + z) ^ (n - i) * (n.choose i : ℂ) := by
    rw [add_assoc, add_pow]
  rw [h1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hcoef : ((n.choose i : ℕ) : ℂ) * (((n - i).choose j : ℕ) : ℂ) =
      (n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ)) := by
    have h1 : (n.choose i) * i.factorial * (n - i).factorial = n.factorial := Nat.choose_mul_factorial_mul_factorial hi'
    have h2 : ((n - i).choose j) * j.factorial * (n - i - j).factorial = (n - i).factorial :=
      Nat.choose_mul_factorial_mul_factorial hj'
    have hi0 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hj0 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk0 : ((n - i - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero hi0 hj0) hk0)]
    have h1c : ((n.choose i : ℕ) : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by exact_mod_cast h1
    have h2c : (((n - i).choose j : ℕ) : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ) = ((n - i).factorial : ℂ) := by
      exact_mod_cast h2
    rw [← h1c, ← h2c]; ring
  rw [← hcoef]; ring

theorem bracket_eq (m j l : ℕ) (a₃ c ē : ZMod 2) :
    ((-1 : ℂ) ^ (j + l) + (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (-1 : ℂ) ^ (m + l) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ c.val * (-1 : ℂ) ^ j + (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ m) =
    if ((j : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((l : ZMod 2) = ē + c) then
      4 * (-1 : ℂ) ^ ((a₃ + (m : ZMod 2) + ē).val) else 0 := by
  have key : ∀ n : ℕ, (-1 : ℂ) ^ n = (-1 : ℂ) ^ ((n : ZMod 2).val) := fun n => by
    rw [ZMod.val_natCast]; exact neg_one_pow_eq_pow_mod_two (R := ℂ) n
  have hv : ∀ x y : ZMod 2, (-1 : ℂ) ^ ((x + y).val) = (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ y.val := fun x y => by
    rw [← pow_add, ZMod.val_add]; exact (neg_one_pow_eq_pow_mod_two (R := ℂ) _).symm
  have h0 : ((0 : ZMod 2)).val = 0 := rfl
  have h1 : ((1 : ZMod 2)).val = 1 := rfl
  rw [pow_add, pow_add, key j, key l, key m, hv, hv]
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  generalize (j : ZMod 2) = xj, (l : ZMod 2) = xl, (m : ZMod 2) = xm
  rcases h2 xj with rfl | rfl <;> rcases h2 xl with rfl | rfl <;> rcases h2 xm with rfl | rfl <;>
    rcases h2 a₃ with rfl | rfl <;> rcases h2 c with rfl | rfl <;> rcases h2 ē with rfl | rfl <;>
    simp [h0, h1, h11] <;> norm_num

theorem add_add_pow_cube (x y z : ℂ) (n N : ℕ) (hN : n < N) :
    (x + y + z) ^ n = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, ∑ l ∈ Finset.range N,
      if i + j + l = n then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) *
        x ^ i * y ^ j * z ^ l else 0 := by
  classical
  rw [add_add_pow]

  have hl : ∀ i j : ℕ, (∑ l ∈ Finset.range N,
      (if i + j + l = n then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) *
        x ^ i * y ^ j * z ^ l else 0)) =
      if i + j ≤ n then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
        x ^ i * y ^ j * z ^ (n - i - j) else 0 := by
    intro i j
    by_cases hij : i + j ≤ n
    · rw [if_pos hij]
      have hcong : ∀ l ∈ Finset.range N,
          (if i + j + l = n then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ))) *
            x ^ i * y ^ j * z ^ l else 0) =
          (if l = n - i - j then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
            x ^ i * y ^ j * z ^ (n - i - j) else 0) := by
        intro l _
        by_cases h : l = n - i - j
        · subst h; rw [if_pos (by omega), if_pos rfl]
        · rw [if_neg (by omega), if_neg h]
      rw [Finset.sum_congr rfl hcong, Finset.sum_ite_eq']
      rw [if_pos (Finset.mem_range.mpr (by omega))]
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg (by omega)]
  simp_rw [hl]

  symm
  rw [← Finset.sum_range_add_sum_Ico _ (show n + 1 ≤ N by omega)]
  have htail : ∑ i ∈ Finset.Ico (n + 1) N, ∑ j ∈ Finset.range N,
      (if i + j ≤ n then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
        x ^ i * y ^ j * z ^ (n - i - j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.mem_Ico] at hi
    rw [if_neg (by omega)]
  rw [htail, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← Finset.sum_range_add_sum_Ico _ (show n - i + 1 ≤ N by omega)]
  have htail2 : ∑ j ∈ Finset.Ico (n - i + 1) N,
      (if i + j ≤ n then ((n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * ((n - i - j).factorial : ℂ))) *
        x ^ i * y ^ j * z ^ (n - i - j) else 0) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [if_neg (by omega)]
  rw [htail2, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [if_pos (by omega)]

theorem bracket2_eq (i j l : ℕ) (a₃ ē : ZMod 2) (Fp Fm : ℂ) :
    (Fp * (-1 : ℂ) ^ (j + l) + (-1 : ℂ) ^ a₃.val * Fm * (-1 : ℂ) ^ (i + j) +
      (-1 : ℂ) ^ ē.val * Fm * (-1 : ℂ) ^ j + (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * Fp * (-1 : ℂ) ^ (i + j + l)) =
    if ((i : ZMod 2) = ē + a₃) then
      2 * ((-1 : ℂ) ^ (j + l) * (Fp + (-1 : ℂ) ^ ((ē + (l : ZMod 2)).val) * Fm)) else 0 := by
  have key : ∀ n : ℕ, (-1 : ℂ) ^ n = (-1 : ℂ) ^ ((n : ZMod 2).val) := fun n => by
    rw [ZMod.val_natCast]; exact neg_one_pow_eq_pow_mod_two (R := ℂ) n
  have hv : ∀ x y : ZMod 2, (-1 : ℂ) ^ ((x + y).val) = (-1 : ℂ) ^ x.val * (-1 : ℂ) ^ y.val := fun x y => by
    rw [← pow_add, ZMod.val_add]; exact (neg_one_pow_eq_pow_mod_two (R := ℂ) _).symm
  have h0 : ((0 : ZMod 2)).val = 0 := rfl
  have h1 : ((1 : ZMod 2)).val = 1 := rfl
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [pow_add, pow_add, pow_add, pow_add, key i, key l, hv]
  generalize (i : ZMod 2) = xi, (l : ZMod 2) = xl
  rcases h2 xi with rfl | rfl <;> rcases h2 xl with rfl | rfl <;>
    rcases h2 a₃ with rfl | rfl <;> rcases h2 ē with rfl | rfl <;>
    simp [h0, h1, h11] <;> ring

end HFR

theorem solution
    (m : ℕ) (a₃ ē : ZMod 2) (Fp Fm u v w : ℂ) :
    (Fp * ∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (u - v - w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ a₃.val * Fm * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (-u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * Fm * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * Fp * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (-u - v - w) ^ (m - 2 * r)) =
      2 * ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = ē + a₃)),
          ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) /
              ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                (4 * (Real.pi : ℂ)) ^ T.1.1)) *
            (-1 : ℂ) ^ (T.2.1 + T.2.2) * (Fp + (-1 : ℂ) ^ (ē + (T.2.2 : ZMod 2)).val * Fm) *
            u ^ T.1.2 * v ^ T.2.1 * w ^ T.2.2 := by
  classical
  have hfac : ∀ k : ℕ, (k.factorial : ℂ) ≠ 0 := fun k => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hpi : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

  have hR : 2 * ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = ē + a₃)),
          ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) /
              ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                (4 * (Real.pi : ℂ)) ^ T.1.1)) *
            (-1 : ℂ) ^ (T.2.1 + T.2.2) * (Fp + (-1 : ℂ) ^ (ē + (T.2.2 : ZMod 2)).val * Fm) *
            u ^ T.1.2 * v ^ T.2.1 * w ^ T.2.2
      = ∑ r ∈ Finset.range (m / 2 + 1), ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          ∑ l ∈ Finset.range (m + 1),
            if i + j + l + 2 * r = m ∧ ((i : ZMod 2) = ē + a₃) then
              2 * (((-1 : ℂ) ^ r * (m.factorial : ℂ) /
                ((r.factorial : ℂ) * (i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ r)) * (-1 : ℂ) ^ (j + l) * (Fp + (-1 : ℂ) ^ (ē + (l : ZMod 2)).val * Fm) *
                u ^ i * v ^ j * w ^ l)
            else 0 := by
    rw [Finset.mul_sum, Finset.sum_filter, Finset.sum_product, Finset.sum_product]
    simp only [Finset.sum_product]
    symm
    apply Finset.sum_subset
    · intro r hr
      simp only [Finset.mem_range] at hr ⊢
      omega
    · intro r hr hr'
      simp only [Finset.mem_range, not_lt] at hr hr'
      apply Finset.sum_eq_zero; intro i _
      apply Finset.sum_eq_zero; intro j _
      apply Finset.sum_eq_zero; intro l _
      rw [if_neg]
      rintro ⟨h, -⟩
      omega
  rw [hR]

  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : 2 * r ≤ m := by
    simp only [Finset.mem_range] at hr; omega
  set n := m - 2 * r with hn
  have hnN : n < m + 1 := by omega
  have hnr : ∀ i j l : ℕ, (i + j + l + 2 * r = m ↔ i + j + l = n) := by intro i j l; omega
  have e1 := HFR.add_add_pow_cube u (-v) (-w) n (m + 1) hnN
  have e2 := HFR.add_add_pow_cube (-u) (-v) w n (m + 1) hnN
  have e3 := HFR.add_add_pow_cube u (-v) w n (m + 1) hnN
  have e4 := HFR.add_add_pow_cube (-u) (-v) (-w) n (m + 1) hnN
  rw [show u - v - w = u + -v + -w by ring, show -u - v + w = -u + -v + w by ring,
    show u - v + w = u + -v + w by ring, show -u - v - w = -u + -v + -w by ring, e1, e2, e3, e4]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  set C : ℂ := (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * (n.factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) with hC
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases heq : i + j + l = n
  · have heq' : i + j + l + 2 * r = m := (hnr i j l).mpr heq
    simp only [if_pos heq, heq', true_and]
    rw [neg_pow u i, neg_pow v j, neg_pow w l]
    set D : ℂ := (n.factorial : ℂ) / ((i.factorial : ℂ) * (j.factorial : ℂ) * (l.factorial : ℂ)) with hD
    set sa : ℂ := (-1 : ℂ) ^ a₃.val with hsa
    set se : ℂ := (-1 : ℂ) ^ ē.val with hse
    have key :
        Fp * (C * (D * u ^ i * ((-1) ^ j * v ^ j) * ((-1) ^ l * w ^ l))) +
          sa * Fm * (C * (D * ((-1) ^ i * u ^ i) * ((-1) ^ j * v ^ j) * w ^ l)) +
          se * Fm * (C * (D * u ^ i * ((-1) ^ j * v ^ j) * w ^ l)) +
          se * sa * Fp * (C * (D * ((-1) ^ i * u ^ i) * ((-1) ^ j * v ^ j) * ((-1) ^ l * w ^ l)))
        = (C * D * (u ^ i * v ^ j * w ^ l)) *
          (Fp * (-1 : ℂ) ^ (j + l) + sa * Fm * (-1 : ℂ) ^ (i + j) + se * Fm * (-1 : ℂ) ^ j +
            se * sa * Fp * (-1 : ℂ) ^ (i + j + l)) := by
      ring
    rw [key, hsa, hse, HFR.bracket2_eq i j l a₃ ē Fp Fm]
    by_cases hP : ((i : ZMod 2) = ē + a₃)
    · rw [if_pos hP, if_pos hP, hC, hD]
      have hnfac : (n.factorial : ℂ) ≠ 0 := hfac _
      have hrfac : (r.factorial : ℂ) ≠ 0 := hfac _
      have hifac : (i.factorial : ℂ) ≠ 0 := hfac _
      have hjfac : (j.factorial : ℂ) ≠ 0 := hfac _
      have hlfac : (l.factorial : ℂ) ≠ 0 := hfac _
      have hpir : (4 * (Real.pi : ℂ)) ^ r ≠ 0 := pow_ne_zero _ hpi
      field_simp
    · rw [if_neg hP, if_neg hP, mul_zero]
  · have hne' : ¬ (i + j + l + 2 * r = m ∧ ((i : ZMod 2) = ē + a₃)) := by
      rintro ⟨h, -⟩; exact heq ((hnr i j l).mp h)
    simp only [if_neg heq, if_neg hne', mul_zero, add_zero]

end S_LanglandsTunnell_hermite_fourfold_twoSheet_reflection_eq_sum_filter
end P2MW
export P2MW.S_LanglandsTunnell_hermite_fourfold_twoSheet_reflection_eq_sum_filter (solution)
