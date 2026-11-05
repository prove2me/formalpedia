-- Prove2me | solution 1 for LL_Decomp1543a.geom_dyadic
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:05:26.412924+00:00
-- url     : https://prove2.me/submissions/df17fd1a-c2e5-4df6-92dc-de638bb83302

import Mathlib
import Definitions.Def_LL_Decomp1543a_e
import Definitions.Def_LL_Decomp1543a_nint
import Definitions.Def_LL_Decomp1543a_minK

open Real Finset ArithmeticFunction

namespace VaAAux
open LL_Decomp1543a

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  have : (2 * (π : ℂ) * Complex.I * (x : ℂ)) = ((2 * π * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem e_int (θ : ℝ) (t : ℤ) : e (θ * (t : ℝ)) = (e θ) ^ t := by
  unfold e
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast; ring

theorem e_sub_one_ge (θ : ℝ) : 4 * nint θ ≤ ‖e θ - 1‖ := by
  set s := θ - round θ with hs
  have h1 : e θ = Complex.exp (Complex.I * ((2 * π * s : ℝ) : ℂ)) := by
    unfold e
    have : (2 * (π : ℂ) * Complex.I * (θ : ℂ)) =
        Complex.I * ((2 * π * s : ℝ) : ℂ) + ((round θ : ℤ) : ℂ) * (2 * π * Complex.I) := by
      simp only [hs]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, Complex.norm_exp_I_mul_ofReal_sub_one]
  have h2 : 2 * π * s / 2 = π * s := by ring
  rw [h2]
  have habs : |s| ≤ 1 / 2 := abs_sub_round θ
  have key : 2 * |s| ≤ Real.sin (π * |s|) := by
    have := Real.mul_le_sin (x := π * |s|) (by positivity) (by nlinarith [Real.pi_pos])
    have h3 : 2 / π * (π * |s|) = 2 * |s| := by field_simp
    linarith
  have hfin : 2 * |s| ≤ |Real.sin (π * s)| := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h] at key ⊢
      have : 0 ≤ Real.sin (π * s) := le_trans (by positivity) key
      rw [abs_of_nonneg this]; exact key
    · rw [abs_of_nonpos h] at key ⊢
      have hsn : Real.sin (π * -s) = - Real.sin (π * s) := by rw [mul_neg, Real.sin_neg]
      rw [hsn] at key
      have : Real.sin (π * s) ≤ 0 := by linarith [le_trans (by linarith : (0:ℝ) ≤ 2 * -s) key]
      rw [abs_of_nonpos this]; linarith
  have h4 : nint θ = |s| := rfl
  rw [Real.norm_eq_abs, abs_mul, abs_two, h4]
  linarith

theorem tel (z : ℂ) (hz : z ≠ 0) (A : ℤ) (n : ℕ) :
    (z - 1) * ∑ t ∈ Ioc A (A + n), z ^ t = z ^ (A + n + 1) - z ^ (A + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hI : Ioc A (A + ((n + 1 : ℕ) : ℤ)) = insert (A + ((n : ℕ) : ℤ) + 1) (Ioc A (A + n)) := by
      ext t; simp only [mem_Ioc, mem_insert]; push_cast; omega
    have hnm : A + ((n : ℕ) : ℤ) + 1 ∉ Ioc A (A + n) := by simp
    rw [hI, sum_insert hnm, mul_add, ih]
    have h5 : A + ((n + 1 : ℕ) : ℤ) + 1 = (A + n + 1) + 1 := by push_cast; ring
    rw [h5, zpow_add_one₀ hz (A + n + 1)]
    ring

theorem geom_gen (θ X : ℝ) (hX : 0 ≤ X) (A B : ℤ) (h : (B : ℝ) - A ≤ X) :
    ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK X θ := by
  have hX' : ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ X := by
    calc ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ ∑ t ∈ Ioc A B, ‖e (θ * t)‖ := norm_sum_le _ _
      _ = ((Ioc A B).card : ℝ) := by simp [norm_e]
      _ ≤ X := by
        rw [Int.card_Ioc]
        by_cases hAB : A ≤ B
        · rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.2 hAB)]
          push_cast; exact h
        · have : (B - A).toNat = 0 := Int.toNat_eq_zero.2 (by omega)
          rw [this]; simpa using hX
  unfold minK
  split_ifs with h0
  · exact hX'
  · refine le_min hX' ?_
    have hpos : 0 < nint θ := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
    by_cases hAB : A < B
    · set z := e θ with hzdef
      have hz1 : ‖z‖ = 1 := norm_e θ
      have hz : z ≠ 0 := by intro h0; rw [h0] at hz1; simp at hz1
      have hsum : ∑ t ∈ Ioc A B, e (θ * t) = ∑ t ∈ Ioc A B, z ^ t :=
        sum_congr rfl (fun t _ => e_int θ t)
      have hn : A + (((B - A).toNat : ℕ) : ℤ) = B := by omega
      have htel := tel z hz A (B - A).toNat
      rw [hn] at htel
      have hnorm : ‖z - 1‖ * ‖∑ t ∈ Ioc A B, z ^ t‖ ≤ 2 := by
        rw [← norm_mul, htel]
        calc ‖z ^ (B + 1) - z ^ (A + 1)‖ ≤ ‖z ^ (B + 1)‖ + ‖z ^ (A + 1)‖ := norm_sub_le _ _
          _ = 2 := by simp [norm_zpow, hz1]; norm_num
      have hge := e_sub_one_ge θ
      rw [hsum]
      have hS0 := norm_nonneg (∑ t ∈ Ioc A B, z ^ t)
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    · rw [Ioc_eq_empty hAB]
      simp only [sum_empty, norm_zero]
      positivity

end VaAAux

open LL_Decomp1543a in
theorem solution (θ M : ℝ) (hM : 0 ≤ M) (A B : ℤ) (hA : ⌊M⌋ ≤ A) (hB : B ≤ ⌊2 * M⌋) :
    ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ := by
  apply VaAAux.geom_gen θ _ (by linarith) A B
  have h1 : ((⌊2 * M⌋ : ℤ) : ℝ) ≤ 2 * M := Int.floor_le _
  have h2 : M < (⌊M⌋ : ℝ) + 1 := Int.lt_floor_add_one M
  have h3 : (⌊M⌋ : ℝ) ≤ M := Int.floor_le M
  have h4 : ⌊2 * M⌋ ≤ 2 * ⌊M⌋ + 1 := by
    have : ((⌊2 * M⌋ : ℤ) : ℝ) < 2 * ⌊M⌋ + 2 := by linarith
    have : ⌊2 * M⌋ < 2 * ⌊M⌋ + 2 := by exact_mod_cast this
    omega
  have hBr : (B : ℝ) ≤ ⌊2 * M⌋ := by exact_mod_cast hB
  have hAr : (⌊M⌋ : ℝ) ≤ A := by exact_mod_cast hA
  rcases le_or_gt ⌊2 * M⌋ (2 * ⌊M⌋) with h5 | h5
  · have : ((⌊2 * M⌋ : ℤ) : ℝ) ≤ 2 * ⌊M⌋ := by exact_mod_cast h5
    linarith
  · have h6 : ⌊2 * M⌋ = 2 * ⌊M⌋ + 1 := by omega
    have : ((⌊2 * M⌋ : ℤ) : ℝ) = 2 * ⌊M⌋ + 1 := by rw [h6]; push_cast; ring
    linarith
