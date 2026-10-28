-- Prove2me | solution 1 for LL_Linnik1536a.exp_le_even_partial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:51:06.964363+00:00
-- url     : https://prove2.me/submissions/20961a8d-cda9-438a-ba45-607b19cf1c2f

import Mathlib
import Definitions.Def_LL_Linnik1536a_Gpow
import Definitions.Def_LL_Linnik1536a_Spow
import Definitions.Def_LL_Linnik1536a_EL
import Definitions.Def_LL_Linnik1536a_devSet
open Real MeasureTheory Finset

namespace A3S89LLe

lemma term_le {r : ℝ} {n : ℕ} (hr : 0 ≤ r) (hrn : r ≤ n) (i : ℕ) :
    r ^ (2 * n + i) / ((2 * n + i).factorial : ℝ) ≤ Real.exp r * (1 / 2) ^ i := by
  induction i with
  | zero => simpa using Real.pow_div_factorial_le_exp (x := r) hr (2 * n)
  | succ i ih =>
    have hk : r ^ (2 * n + (i + 1)) / ((2 * n + (i + 1)).factorial : ℝ)
        = r ^ (2 * n + i) / ((2 * n + i).factorial : ℝ) * (r / ((2 * n + i : ℕ) + 1 : ℝ)) := by
      rw [show 2 * n + (i + 1) = (2 * n + i) + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    rw [hk]
    have hpos : (0 : ℝ) < ((2 * n + i : ℕ) : ℝ) + 1 := by positivity
    have h1 : r / ((2 * n + i : ℕ) + 1 : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hpos]
      push_cast
      have : (0:ℝ) ≤ i := by positivity
      nlinarith
    have h0 : 0 ≤ r / ((2 * n + i : ℕ) + 1 : ℝ) := by positivity
    have ht : 0 ≤ r ^ (2 * n + i) / ((2 * n + i).factorial : ℝ) := by positivity
    calc _ ≤ Real.exp r * (1 / 2) ^ i * (1 / 2) := mul_le_mul ih h1 h0 (by positivity)
      _ = _ := by rw [pow_succ]; ring

end A3S89LLe

theorem solution {A r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A) :
    Real.exp r ≤
      2 * ∑ j ∈ range (2 * ⌈A⌉₊ + 1), r ^ (2 * j) / ((2 * j).factorial : ℝ) + 1 := by
  set n := ⌈A⌉₊ with hn
  have hrn : r ≤ n := hrA.trans (Nat.le_ceil A)
  set f : ℕ → ℝ := fun j => r ^ (2 * j) / ((2 * j).factorial : ℝ) with hf
  have hs := Real.hasSum_cosh r
  have hsum : Summable f := hs.summable
  have hsplit := hsum.sum_add_tsum_nat_add (2 * n + 1)
  rw [hs.tsum_eq] at hsplit
  -- tail bound
  have hen : Real.exp r ≤ 4 ^ n := by
    calc Real.exp r ≤ Real.exp n := Real.exp_le_exp.mpr hrn
      _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 4 ^ n := by
        gcongr
        linarith [Real.exp_one_lt_d9]
  have hbound : ∀ j, f (j + (2 * n + 1)) ≤ (1 / 4) * (1 / 2) ^ j := by
    intro j
    have := A3S89LLe.term_le hr hrn (2 * j + 2 * n + 2)
    simp only [hf]
    rw [show 2 * (j + (2 * n + 1)) = 2 * n + (2 * j + 2 * n + 2) by ring]
    refine this.trans ?_
    have h4 : (4:ℝ) ^ n * (1 / 2) ^ (2 * n) = 1 := by
      rw [pow_mul, ← mul_pow]; norm_num
    calc Real.exp r * (1 / 2) ^ (2 * j + 2 * n + 2)
        ≤ 4 ^ n * (1 / 2) ^ (2 * j + 2 * n + 2) := by gcongr
      _ = (4 ^ n * (1 / 2) ^ (2 * n)) * (1 / 4) * (1 / 2) ^ (2 * j) := by
        rw [pow_add, pow_add]; ring
      _ ≤ (1 / 4) * (1 / 2) ^ j := by
        rw [h4, one_mul]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
  have hgeo : Summable (fun j : ℕ => (1 / 4 : ℝ) * (1 / 2) ^ j) :=
    (summable_geometric_two).mul_left _
  have htail : ∑' j, f (j + (2 * n + 1)) ≤ 1 / 2 := by
    calc ∑' j, f (j + (2 * n + 1)) ≤ ∑' j : ℕ, (1 / 4 : ℝ) * (1 / 2) ^ j :=
          Summable.tsum_le_tsum hbound ((summable_nat_add_iff _).mpr hsum) hgeo
      _ = 1 / 2 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  have hc := Real.cosh_eq r
  have hneg := Real.exp_pos (-r)
  have : Real.exp r ≤ 2 * Real.cosh r := by rw [hc]; linarith
  linarith
