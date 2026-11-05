-- Prove2me | solution 1 for LL_Decomp1543a.J_props
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:24.728525+00:00
-- url     : https://prove2.me/submissions/01327487-6a68-4627-8a65-6acf1c336d6f

import Mathlib
import Definitions.Def_LL_Decomp1543a_Jn

open Real Finset ArithmeticFunction

namespace VaAAux

theorem two_pow_logb (y : ℝ) (hy : 0 < y) : (2 : ℝ) ^ (Real.log y / Real.log 2) = y :=
  Real.rpow_logb (by norm_num) (by norm_num) hy

open LL_Decomp1543a in
theorem Jn_le (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U * V ≤ N) :
    (2 : ℝ) ^ (Jn N U V - 1) * V ≤ N / U := by
  have hUV0 : 0 < U * V := mul_pos hU hV
  have hy : 1 ≤ (N : ℝ) / (U * V) := by rw [le_div_iff₀ hUV0]; linarith
  have hx0 : 0 ≤ Real.log ((N : ℝ) / (U * V)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hy) (Real.log_pos (by norm_num)).le
  have h1 : Jn N U V - 1 = ⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ := by
    unfold Jn; omega
  have h2 : (2 : ℝ) ^ (Jn N U V - 1) ≤ (N : ℝ) / (U * V) := by
    rw [h1, ← Real.rpow_natCast]
    calc (2 : ℝ) ^ ((⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (Real.log ((N : ℝ) / (U * V)) / Real.log 2) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.floor_le hx0)
      _ = (N : ℝ) / (U * V) := two_pow_logb _ (by linarith)
  calc (2 : ℝ) ^ (Jn N U V - 1) * V ≤ (N : ℝ) / (U * V) * V :=
        mul_le_mul_of_nonneg_right h2 hV.le
    _ = N / U := by field_simp

open LL_Decomp1543a in
theorem lt_two_pow_Jn (N : ℕ) (U V : ℝ) (hN : 0 < N) (hU : 0 < U) (hV : 0 < V) :
    (N : ℝ) / U < (2 : ℝ) ^ (Jn N U V) * V := by
  have hUV0 : 0 < U * V := mul_pos hU hV
  have hy : 0 < (N : ℝ) / (U * V) := by positivity
  have h1 : Real.log ((N : ℝ) / (U * V)) / Real.log 2 <
      ((⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have h2 : (N : ℝ) / (U * V) < (2 : ℝ) ^ (Jn N U V) := by
    have : Jn N U V = ⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ + 1 := rfl
    rw [this, ← Real.rpow_natCast]
    calc (N : ℝ) / (U * V) = (2 : ℝ) ^ (Real.log ((N : ℝ) / (U * V)) / Real.log 2) :=
          (two_pow_logb _ hy).symm
      _ < _ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
  calc (N : ℝ) / U = (N : ℝ) / (U * V) * V := by field_simp
    _ < (2 : ℝ) ^ (Jn N U V) * V := mul_lt_mul_of_pos_right h2 hV

end VaAAux

open LL_Decomp1543a in
theorem solution (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U * V ≤ N) :
    2 ^ (Jn N U V - 1) * V ≤ N / U ∧
      (Jn N U V : ℝ) ≤ 1 + Real.log (N / (U * V)) / Real.log 2 := by
  refine ⟨VaAAux.Jn_le N U V hU hV hUV, ?_⟩
  have hUV0 : 0 < U * V := mul_pos hU hV
  have hy : 1 ≤ (N : ℝ) / (U * V) := by rw [le_div_iff₀ hUV0]; linarith
  have hx0 : 0 ≤ Real.log ((N : ℝ) / (U * V)) / Real.log 2 :=
    div_nonneg (Real.log_nonneg hy) (Real.log_pos (by norm_num)).le
  have : (Jn N U V : ℝ) = (⌊Real.log ((N : ℝ) / (U * V)) / Real.log 2⌋₊ : ℝ) + 1 := by
    unfold Jn; push_cast; rfl
  rw [this]
  linarith [Nat.floor_le hx0]
