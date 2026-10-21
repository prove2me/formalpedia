-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.period_columnFunction_norm_le_of_factorized_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-20T12:59:04.159677+00:00
-- url     : https://prove2.me/submissions/6d0aabcd-289e-47ed-9aa5-8f27d114494a

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansion_CollisionAnalyticHelpers

open scoped BigOperators Topology

theorem solution
    {m : ℕ} (h : ℕ) (a : Fin m → ℕ) (A : Fin m →₀ ℕ)
    {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ ≤
      Real.exp ((h : ℝ) * R) * Real.exp ((∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
  let B : ℕ := ∏ i, (a i).choose (A i)
  let D : ℕ := ∑ i : Fin m, (a i - A i)
  let N : ℕ := ∑ i : Fin m, a i
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hB : (B : ℝ) ≤ (2 : ℝ) ^ N := by
    have hnat : B ≤ 2 ^ N := by
      calc
        B ≤ ∏ i : Fin m, (2 : ℕ) ^ a i :=
          Finset.prod_le_prod' (fun i _ => Nat.choose_le_two_pow (a i) (A i))
        _ = 2 ^ N := Finset.prod_pow_eq_pow_sum Finset.univ a 2
    exact_mod_cast hnat
  have hD : D ≤ N :=
    Finset.sum_le_sum (fun i _ => Nat.sub_le (a i) (A i))
  have hBR : (B : ℝ) * R ^ D ≤ (2 * R) ^ N := by
    calc
      (B : ℝ) * R ^ D ≤ (2 : ℝ) ^ N * R ^ N :=
        mul_le_mul hB (pow_le_pow_right₀ hR hD)
          (pow_nonneg hR0 _) (by positivity)
      _ = (2 * R) ^ N := (mul_pow 2 R N).symm
  have hpower : (2 * R) ^ N =
      Real.exp ((∑ i, (a i : ℝ)) * Real.log (2 * R)) := by
    have hN : (N : ℝ) = ∑ i, (a i : ℝ) := by simp [N]
    rw [← hN, Real.exp_nat_mul, Real.exp_log (mul_pos (by norm_num) hRpos)]
  have hre : ((h : ℂ) * z).re ≤ (h : ℝ) * R := by
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using
      mul_le_mul_of_nonneg_left ((Complex.re_le_norm z).trans hz) (Nat.cast_nonneg h)
  have hexp : ‖Complex.exp ((h : ℂ) * z)‖ ≤ Real.exp ((h : ℝ) * R) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hre
  have hnorm :
      ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ ≤
        Real.exp ((h : ℝ) * R) * ((B : ℝ) * R ^ D) := by
    calc
      ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ =
          (B : ℝ) * ‖Complex.exp ((h : ℂ) * z)‖ * ‖z‖ ^ D := by
        change ‖(B : ℂ) * Complex.exp ((h : ℂ) * z) * z ^ D‖ = _
        rw [norm_mul, norm_mul, Complex.norm_natCast, norm_pow]
      _ ≤ (B : ℝ) * Real.exp ((h : ℝ) * R) * R ^ D :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg B))
          (pow_le_pow_left₀ (norm_nonneg z) hz D)
          (pow_nonneg (norm_nonneg z) D)
          (mul_nonneg (Nat.cast_nonneg B) (Real.exp_nonneg _))
      _ = Real.exp ((h : ℝ) * R) * ((B : ℝ) * R ^ D) := by ring
  calc
    ‖OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.CollisionAnalytic.columnFunction h a A z‖ ≤
        Real.exp ((h : ℝ) * R) * ((B : ℝ) * R ^ D) := hnorm
    _ ≤ Real.exp ((h : ℝ) * R) * (2 * R) ^ N :=
      mul_le_mul_of_nonneg_left hBR (Real.exp_nonneg _)
    _ = Real.exp ((h : ℝ) * R) *
        Real.exp ((∑ i, (a i : ℝ)) * Real.log (2 * R)) := by rw [hpower]