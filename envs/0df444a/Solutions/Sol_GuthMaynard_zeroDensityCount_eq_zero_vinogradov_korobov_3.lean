-- Prove2me | solution 3 for GuthMaynard.zeroDensityCount_eq_zero_vinogradov_korobov
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-14T21:42:37.961659+00:00
-- url     : https://prove2.me/submissions/4feb95b2-b131-4b12-806f-cd0514785bf5

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts
import Theorems.Thm_Zeta0EqZeta
import Theorems.Thm_ExponentialSums_kusmin_landau
import Theorems.Thm_OAI_TwoPointCorrelations_halasz_log_dirichlet_block
import Theorems.Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg

set_option autoImplicit false

section
/-!
# A weak Richert bound `|ζ(σ+it)| ≤ A|t|^{B(1-σ)^{3/2}} log^7|t|` for `2/3 ≤ σ ≤ 1`

The approximate formula `ζ(s) = ∑_{n ≤ t} n^{-s} + O(1)` (from `Zeta0EqZeta` with `N ≈ t²` and
`ExponentialSums.kusmin_landau` for `t < n ≤ t²`) reduces the bound to dyadic blocks
`∑_{N ≤ n < N + H} n^{-s}`, `8 ≤ N ≤ t`, `H ≤ N`, each of which is bounded by
`OAI.TwoPointCorrelations.halasz_log_dirichlet_block` with `lam = log t / log N ≥ 1`.
-/

open Complex Filter Topology Set

namespace GuthMaynard.CitedZeros.VK2Rich

/-- Abel summation step: `∑_{M<n≤R} a n z n - a R S R` is bounded by `(a(M+1) - a R) B`. -/
theorem abel_aux (a : ℕ → ℝ) (z : ℕ → ℂ) (B : ℝ) (M Rm : ℕ)
    (ha : ∀ n, M < n → a (n + 1) ≤ a n)
    (hB : ∀ R', M < R' → R' ≤ Rm → ‖∑ n ∈ Finset.Ioc M R', z n‖ ≤ B) :
    ∀ R, M + 1 ≤ R → R ≤ Rm → ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n -
        (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ ≤ (a (M + 1) - a R) * B := by
  intro R hR
  induction R, hR using Nat.le_induction with
  | base =>
    intro _
    simp [Nat.Ioc_succ_singleton]
  | succ R hR ih =>
    intro hRm
    have ih := ih (by omega)
    have hMR : M < R := by omega
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
    have heq : (∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n + (a (R + 1) : ℂ) * z (R + 1)) -
        (a (R + 1) : ℂ) * (∑ n ∈ Finset.Ioc M R, z n + z (R + 1)) =
        (∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n - (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n) +
          ((a R - a (R + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc M R, z n := by
      push_cast; ring
    rw [heq]
    have h1 := hB R hMR (by omega)
    have h2 : 0 ≤ a R - a (R + 1) := by linarith [ha R hMR]
    calc _ ≤ ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n - (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ +
          ‖((a R - a (R + 1) : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ := norm_add_le _ _
      _ ≤ (a (M + 1) - a R) * B + (a R - a (R + 1)) * B := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h2]
          gcongr
      _ = _ := by ring

/-- Abel's inequality. -/
theorem abel_ineq (a : ℕ → ℝ) (z : ℕ → ℂ) (B : ℝ) (M R : ℕ) (hR : M + 1 ≤ R)
    (ha : ∀ n, M < n → a (n + 1) ≤ a n) (ha0 : 0 ≤ a R)
    (hB : ∀ R', M < R' → R' ≤ R → ‖∑ n ∈ Finset.Ioc M R', z n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n‖ ≤ a (M + 1) * B := by
  have h1 := abel_aux a z B M R ha hB R hR le_rfl
  have h2 := hB R (by omega) le_rfl
  calc _ ≤ ‖∑ n ∈ Finset.Ioc M R, (a n : ℂ) * z n -
        (a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ + ‖(a R : ℂ) * ∑ n ∈ Finset.Ioc M R, z n‖ :=
        norm_le_norm_sub_add _ _
    _ ≤ (a (M + 1) - a R) * B + a R * B := by
        gcongr
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ha0]
        gcongr
    _ = _ := by ring

theorem log_succ_sub_le (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn'.ne']
  have := Real.log_le_sub_one_of_pos (x := ((n : ℝ) + 1) / n) (by positivity)
  have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
  linarith

theorem le_log_succ_sub (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (x := (n : ℝ) / (n + 1)) (by positivity)
  rw [Real.log_div hn'.ne' (by positivity)] at h
  have e : (n : ℝ) / (n + 1) - 1 = -(1 / (n + 1)) := by field_simp; ring
  linarith

theorem log_diff_anti (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) hn'.ne']
  apply Real.log_le_log (by positivity)
  rw [div_le_div_iff₀ (by positivity) hn']
  nlinarith

/-- `n^{-it} = exp(2πi f(n))` with `f(n) = -t log n / (2π)`. -/
theorem cpow_neg_tI_eq (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) =
      Complex.exp (((2 * Real.pi * (-t * Real.log n / (2 * Real.pi)) : ℝ) : ℂ) * I) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn'.ne'), ← Complex.ofReal_log hn'.le]
  congr 1
  have : (2 * Real.pi * (-t * Real.log n / (2 * Real.pi))) = -t * Real.log n := by
    field_simp
  rw [this]; push_cast; ring

/-- `n^{-(σ+it)} = n^{-σ} n^{-it}`. -/
theorem cpow_split (σ t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.ofReal_cpow hn'.le, neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn'.ne')]
  push_cast; ring_nf

/-- Kusmin–Landau on a block: `‖∑_{M<n≤R} n^{-it}‖ ≤ 2π(2M+2)/t`. -/
theorem exp_block (t : ℝ) (ht : 0 < t) (M R : ℕ) (hM1 : 1 ≤ M) (htM : t ≤ M + 1)
    (hR : R ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))‖ ≤
      2 * Real.pi * (2 * M + 2) / t := by
  have hpi := Real.pi_gt_three
  set f : ℕ → ℝ := fun n => -t * Real.log n / (2 * Real.pi) with hf
  set δ : ℝ := (t / (2 * M + 2)) / (2 * Real.pi) with hδ
  have hMpos : (0 : ℝ) < 2 * M + 2 := by positivity
  have hdiff : ∀ n : ℕ, f (n + 1) - f n =
      -(t * (Real.log ((n : ℝ) + 1) - Real.log n)) / (2 * Real.pi) := by
    intro n; simp only [hf]; push_cast; ring
  have hsum : ∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc M R, Complex.exp (((2 * Real.pi * f n : ℝ) : ℂ) * I) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact cpow_neg_tI_eq t n (by omega)
  rw [hsum]
  have hδ0 : 0 < δ := by positivity
  have htM2 : t / (2 * M + 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hMpos]; linarith
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  have key := ExponentialSums.kusmin_landau (f := f) (a := M) (b := R) (m := -1) hδ0 hδ1
    (fun n hn1 hn2 => by
      rw [hdiff]
      have hn : 1 ≤ n := by omega
      have hD := log_succ_sub_le n hn
      have hD0 := le_log_succ_sub n hn
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have htn : t ≤ n := by
        have : (M : ℝ) + 1 ≤ n := by exact_mod_cast hn1
        linarith
      set D := Real.log ((n : ℝ) + 1) - Real.log n
      have htD : t * D ≤ 1 := by
        calc t * D ≤ t * (1 / n) := by gcongr
          _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; exact htn
      rw [hδ]
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [show ((-1 : ℤ) : ℝ) + t / (2 * M + 2) / (2 * Real.pi) =
        (t / (2 * M + 2) - 2 * Real.pi) / (2 * Real.pi) by push_cast; field_simp; ring]
      rw [div_le_div_iff_of_pos_right h2pi]
      linarith)
    (fun n hn1 hn2 => by
      rw [hdiff]
      have hn : 1 ≤ n := by omega
      have hD0 := le_log_succ_sub n hn
      set D := Real.log ((n : ℝ) + 1) - Real.log n
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [hδ, show ((-1 : ℤ) : ℝ) + 1 - t / (2 * M + 2) / (2 * Real.pi) =
        -(t / (2 * M + 2)) / (2 * Real.pi) by push_cast; ring]
      rw [div_le_div_iff_of_pos_right h2pi, neg_le_neg_iff]
      have hnM : (n : ℝ) + 1 ≤ 2 * M + 2 := by
        have : (n : ℝ) ≤ 2 * M := by exact_mod_cast hn2.trans hR
        linarith
      calc t / (2 * M + 2) = t * (1 / (2 * M + 2)) := by ring
        _ ≤ t * (1 / ((n : ℝ) + 1)) := by gcongr
        _ ≤ t * D := by gcongr)
    (fun n hn1 hn2 => by
      have hn : 1 ≤ n := by omega
      have e := hdiff (n + 1)
      rw [hdiff, show n + 2 = n + 1 + 1 by ring, e]
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [div_le_div_iff_of_pos_right h2pi, neg_le_neg_iff]
      have := log_diff_anti n hn
      push_cast
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
      gcongr)
  refine key.trans (le_of_eq ?_)
  rw [hδ]; field_simp

/-- A dyadic block of the Dirichlet polynomial: `‖∑_{M<n≤R} n^{-s}‖ ≤ 4π√(M+1)/t`. -/
theorem block_bound (t σ : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 0 < t) (M R : ℕ) (hM1 : 1 ≤ M)
    (htM : t ≤ M + 1) (hR : R ≤ 2 * M) :
    ‖∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      4 * Real.pi * Real.sqrt ((M : ℝ) + 1) / t := by
  by_cases hRM : M + 1 ≤ R
  swap
  · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
  have hsum : ∑ n ∈ Finset.Ioc M R, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      ∑ n ∈ Finset.Ioc M R, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Ioc] at hn
    exact cpow_split σ t n (by omega)
  rw [hsum]
  have hσ0 : 0 < σ := by linarith
  have h := abel_ineq (fun n : ℕ => (n : ℝ) ^ (-σ))
    (fun n : ℕ => ((n : ℝ) : ℂ) ^ (-((t : ℂ) * I))) (2 * Real.pi * (2 * M + 2) / t) M R hRM
    (fun n hn => by
      have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      show ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-σ)
      rw [Real.rpow_neg (by positivity), Real.rpow_neg hn'.le]
      apply inv_anti₀ (Real.rpow_pos_of_pos hn' _)
      apply Real.rpow_le_rpow hn'.le (by push_cast; linarith) hσ0.le)
    (by positivity)
    (fun R' h1 h2 => exp_block t ht M R' hM1 htM (h2.trans hR))
  refine h.trans ?_
  set x : ℝ := (M : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; linarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
  have hcast : (((M + 1 : ℕ) : ℝ)) = x := by push_cast; rfl
  rw [hcast]
  have hle : x ^ (-σ) ≤ x ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hsq : x ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt x := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow, one_div]; norm_num
  have e : 2 * Real.pi * (2 * (M : ℝ) + 2) / t = 4 * Real.pi * x / t := by rw [hx]; ring
  rw [e]
  calc x ^ (-σ) * (4 * Real.pi * x / t) ≤ x ^ (-(1 / 2 : ℝ)) * (4 * Real.pi * x / t) := by
        gcongr
    _ = 4 * Real.pi * (x / Real.sqrt x) / t := by rw [hsq]; ring
    _ = _ := by rw [Real.div_sqrt]

/-- The middle range `T < n ≤ T 2^K`, summed over dyadic blocks. -/
theorem middle_bound (t σ : ℝ) (hσ : 1 / 2 ≤ σ) (ht : 0 < t) (T : ℕ) (hT1 : 1 ≤ T)
    (htT : t ≤ T + 1) (K : ℕ) :
    ‖∑ n ∈ Finset.Ioc T (T * 2 ^ K), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      16 * Real.pi * Real.sqrt ((T * 2 ^ K : ℕ) : ℝ) / t := by
  induction K with
  | zero => simp; positivity
  | succ K ih =>
    have hM1 : 1 ≤ T * 2 ^ K := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hTM : T ≤ T * 2 ^ K := Nat.le_mul_of_pos_right T (by positivity)
    have h2 : T * 2 ^ (K + 1) = 2 * (T * 2 ^ K) := by ring
    rw [← Finset.sum_Ioc_consecutive _ hTM (by rw [h2]; omega)]
    have hblk := block_bound t σ hσ ht (T * 2 ^ K) (T * 2 ^ (K + 1)) hM1
      (by have : (T : ℝ) ≤ (T * 2 ^ K : ℕ) := by exact_mod_cast hTM
          linarith) (by rw [h2])
    set M := T * 2 ^ K with hMdef
    have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    have hc : ((T * 2 ^ (K + 1) : ℕ) : ℝ) = 2 * (M : ℝ) := by rw [h2]; push_cast; ring
    rw [hc]
    have hs2 : Real.sqrt (2 * (M : ℝ)) = Real.sqrt 2 * Real.sqrt M :=
      Real.sqrt_mul (by norm_num) _
    have hM1' : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt (2 * (M : ℝ)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsqrt2 : (4 : ℝ) / 3 ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have hu : 0 ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
    have hpi := Real.pi_pos
    calc _ ≤ ‖∑ n ∈ Finset.Ioc T M, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ +
          ‖∑ n ∈ Finset.Ioc M (T * 2 ^ (K + 1)), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ :=
          norm_add_le _ _
      _ ≤ 16 * Real.pi * Real.sqrt (M : ℝ) / t + 4 * Real.pi * Real.sqrt (2 * (M : ℝ)) / t := by
          gcongr
          exact hblk.trans (by gcongr)
      _ ≤ _ := by
          rw [← add_div]
          gcongr
          rw [hs2]
          nlinarith [mul_nonneg hpi.le hu]

/-- The Euler–Maclaurin remainder integral. -/
theorem integral_bound (s : ℂ) (hs : 0 < s.re) (N : ℕ) (hN : 0 < N) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (N : ℝ) ^ (-s.re) / (2 * s.re) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : -(s.re + 1) < -1 := by linarith
  have hint := integrableOn_Ioi_rpow_of_lt hlt hN'
  refine (MeasureTheory.norm_integral_le_of_norm_le (g := fun x => (1 / 2 : ℝ) * x ^ (-(s.re + 1)))
    (hint.const_mul _) ?_).trans (le_of_eq ?_)
  · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hN'.trans hx
    have e : ((⌊x⌋ : ℂ) + 1 / 2 - x) = (((⌊x⌋ : ℝ) + 1 / 2 - x : ℝ) : ℂ) := by push_cast; ring
    rw [e, norm_div, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have h1 := Int.floor_le x
    have h2 := Int.lt_floor_add_one x
    have hab : ‖((⌊x⌋ : ℝ) + 1 / 2 - x)‖ ≤ 1 / 2 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    have hre : (s + 1).re = s.re + 1 := by simp
    rw [hre, Real.rpow_neg hx0.le, div_eq_mul_inv]
    gcongr
  · rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hlt hN']
    have : -(s.re + 1) + 1 = -s.re := by ring
    rw [this]
    field_simp

/-- Reindexing the `riemannZeta0` sum. -/
theorem range_sum_eq (s : ℂ) (hs : s ≠ 0) (N T : ℕ) (hTN : T ≤ N) :
    ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s =
      ∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-s) + ∑ n ∈ Finset.Ioc T N, ((n : ℝ) : ℂ) ^ (-s) := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have h0 : 1 / ((0 : ℕ) : ℂ) ^ s = 0 := by simp [Complex.zero_cpow hs]
  rw [h0, zero_add]
  have hI : Finset.Icc 1 T = Finset.Ioc 0 T := by ext n; simp; omega
  have hI2 : Finset.Ico (0 + 1) (N + 1) = Finset.Ioc 0 N := by ext n; simp; omega
  rw [hI, hI2, Finset.sum_Ioc_consecutive _ (Nat.zero_le T) hTN]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.cpow_neg, Complex.ofReal_natCast, one_div]

theorem approx_formula : ∃ K t₀ : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t₀ ≤ t → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 1 →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
      ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ K := by
  refine ⟨16 * Real.pi + 10, 4, by positivity, fun t ht σ hσ0 hσ1 => ?_⟩
  have hpi := Real.pi_pos
  have htpos : 0 < t := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hs0 : s ≠ 0 := by intro h; rw [h] at hsim; simp at hsim; linarith
  have hs1 : s ≠ 1 := by intro h; rw [h] at hsim; simp at hsim; linarith
  set T := ⌊t⌋₊ with hTdef
  have hT1 : 1 ≤ T := Nat.le_floor (by push_cast; linarith)
  have hTt : (T : ℝ) ≤ t := Nat.floor_le htpos.le
  have htT : t ≤ T + 1 := (Nat.lt_floor_add_one t).le
  set L := Nat.log 2 T with hL
  set N := T * 2 ^ L with hNdef
  have hpow : 2 ^ L ≤ T := Nat.pow_log_le_self 2 (by omega)
  have hpow2 : T < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) T
  have hNT : N ≤ T * T := Nat.mul_le_mul_left T hpow
  have hTN2 : T * T ≤ 2 * N := by
    rw [hNdef]; nlinarith [pow_succ 2 L]
  have hTN : T ≤ N := Nat.le_mul_of_pos_right T (by positivity)
  have hN0 : 0 < N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hNTr : (N : ℝ) ≤ (T : ℝ) * T := by exact_mod_cast hNT
  have hTN2r : (T : ℝ) * T ≤ 2 * N := by exact_mod_cast hTN2
  -- `√N ≤ t` and `t ≤ 3 √N`
  have hsqN : Real.sqrt N ≤ t := by
    rw [Real.sqrt_le_left htpos.le]; nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have hsqN0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsqNsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by linarith)
  have ht3 : t ≤ 3 * Real.sqrt N := by
    have h1 : t ≤ 2 * T := by
      have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
      linarith
    nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
  have hz := Zeta0EqZeta (N := N) hN0 (s := s) (by rw [hsre]; linarith) hs1
  rw [← hz]
  unfold riemannZeta0
  rw [range_sum_eq s hs0 N T hTN]
  set A := ∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-s)
  set B := ∑ n ∈ Finset.Ioc T N, ((n : ℝ) : ℂ) ^ (-s) with hB
  set E1 := (-(N : ℂ) ^ (1 - s)) / (1 - s) with hE1
  set E2 := (-(N : ℂ) ^ (-s)) / 2 with hE2
  set J := ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) with hJ
  have hsplit : A + B + E1 + E2 + s * J - A = B + E1 + E2 + s * J := by ring
  rw [hsplit]
  -- the middle range
  have hBb : ‖B‖ ≤ 16 * Real.pi := by
    have := middle_bound t σ hσ0 htpos T hT1 htT L
    rw [← hNdef] at this
    refine this.trans ?_
    rw [div_le_iff₀ htpos]
    nlinarith
  -- `N^{1-s}/(1-s)`
  have hE1b : ‖E1‖ ≤ 1 := by
    rw [hE1, norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN0]
    have hre : (1 - s).re = 1 - σ := by simp [hsre]
    rw [hre]
    have hden : t ≤ ‖1 - s‖ := by
      have := Complex.abs_im_le_norm (1 - s)
      have e : (1 - s).im = -t := by simp [hsim]
      rw [e, abs_neg, abs_of_pos htpos] at this
      exact this
    have hnum : (N : ℝ) ^ (1 - σ) ≤ Real.sqrt N := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
    rw [div_le_one (by linarith)]
    linarith
  have hE2b : ‖E2‖ ≤ 1 / 2 := by
    rw [hE2, norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hN0]
    have hre : (-s).re = -σ := by simp [hsre]
    rw [hre]
    have : (N : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hNr (by linarith)
    simp only [Complex.norm_ofNat]
    linarith
  have hJb : ‖s * J‖ ≤ 6 := by
    have hI := integral_bound s (by rw [hsre]; linarith) N hN0
    rw [hsre] at hI
    have hsn : ‖s‖ ≤ 2 * t := by
      have h1 : ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
        Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg htpos.le] at h1
      linarith
    have hNs : (N : ℝ) ^ (-σ) ≤ 1 / Real.sqrt N := by
      have : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
      refine this.trans (le_of_eq ?_)
      rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow, one_div]; norm_num
    have hNs0 : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
    have h2 : (N : ℝ) ^ (-σ) / (2 * σ) ≤ 1 / Real.sqrt N := by
      rw [div_le_iff₀ (by linarith)]
      have : 0 ≤ 1 / Real.sqrt N := by positivity
      nlinarith
    rw [norm_mul]
    calc ‖s‖ * ‖J‖ ≤ (2 * t) * (1 / Real.sqrt N) := by
          gcongr
          exact hI.trans h2
      _ ≤ 6 := by
          rw [mul_one_div, div_le_iff₀ hsqN0]; linarith
  calc ‖B + E1 + E2 + s * J‖ ≤ ‖B‖ + ‖E1‖ + ‖E2‖ + ‖s * J‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ 16 * Real.pi + 10 := by linarith

/-! ## The blocks `N ≤ n < N + H` with `8 ≤ N ≤ t` -/

theorem eight_rpow_two_thirds_le (N : ℕ) (hN8 : 8 ≤ N) : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) / 2 := by
  have hN8r : (8 : ℝ) ≤ N := by exact_mod_cast hN8
  have hN0 : (0 : ℝ) < N := by linarith
  have h2 : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    calc (2 : ℝ) = ((2 : ℝ) ^ (3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ = (8 : ℝ) ^ (1 / 3 : ℝ) := by norm_num
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hN8r (by norm_num)
  have hsplit : (N : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (1 / 3 : ℝ) = N := by
    rw [← Real.rpow_add hN0]; norm_num
  have hp : 0 ≤ (N : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg hN0.le _
  nlinarith

/-- One block, from `OAI.TwoPointCorrelations.halasz_log_dirichlet_block` with `a = 0` and
`lam = log t / log N`. -/
theorem halasz_block (C : ℝ)
    (hC : ∀ N H : ℕ,
      1 ≤ N → H ≤ N → ∀ a : ℝ, a ∈ Set.Icc (0:ℝ) 1 → ∀ s : ℂ,
      2/3 ≤ s.re → ∀ L lam : ℝ, 0 < L → 1 ≤ Real.log N →
      L = lam * Real.log N → 49/100 ≤ lam →
      (N:ℝ)^(2/3:ℝ) ≤ (N:ℝ)/2 → |s.im| = (N:ℝ)^lam →
      ‖∑ n ∈ Finset.range H, (((N:ℝ)+a+n:ℝ):ℂ)^(-s)‖ ≤
        C*(L+1)^6*Real.exp ((10^9:ℝ)*(max (1-s.re) 0)^(3/2:ℝ)*L)+4)
    (t σ : ℝ) (ht : 1 < t) (hσ : 2 / 3 ≤ σ) (hσ1 : σ ≤ 1) (N H : ℕ) (hN8 : 8 ≤ N) (hH : H ≤ N)
    (hNt : (N : ℝ) ≤ t) :
    ‖∑ n ∈ Finset.Ico N (N + H), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      C * (Real.log t + 1) ^ 6 *
        Real.exp ((10 ^ 9 : ℝ) * (1 - σ) ^ (3 / 2 : ℝ) * Real.log t) + 4 := by
  have hN8r : (8 : ℝ) ≤ N := by exact_mod_cast hN8
  have hN0 : (0 : ℝ) < N := by linarith
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hlogN1 : 1 ≤ Real.log (N : ℝ) := by
    rw [Real.le_log_iff_exp_le hN0]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hN8r
  have hlogN0 : 0 < Real.log (N : ℝ) := by linarith
  have hlogNt : Real.log (N : ℝ) ≤ Real.log t := Real.log_le_log hN0 hNt
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have h := hC N H (by omega) hH 0 ⟨le_rfl, zero_le_one⟩ s (by rw [hsre]; exact hσ)
    (Real.log t) (Real.log t / Real.log N) hlogt hlogN1
    (by field_simp)
    (by rw [le_div_iff₀ hlogN0]; linarith)
    (eight_rpow_two_thirds_le N hN8)
    (by
      rw [hsim, abs_of_pos ht0, Real.rpow_def_of_pos hN0,
        mul_div_cancel₀ _ hlogN0.ne', Real.exp_log ht0])
  rw [hsre, max_eq_left (by linarith)] at h
  refine le_of_eq_of_le (congrArg norm ?_) h
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 2
  push_cast; ring

/-- Dyadic induction: `8 ≤ n ≤ T` is covered by at most `j` blocks when `T < 8·2^j`. -/
theorem dyadic_ind (t σ Bd : ℝ) (hBd0 : 0 ≤ Bd)
    (hblk : ∀ N H : ℕ, 8 ≤ N → H ≤ N → (N : ℝ) ≤ t →
      ‖∑ n ∈ Finset.Ico N (N + H), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ Bd) :
    ∀ j T : ℕ, T < 8 * 2 ^ j → (T : ℝ) ≤ t →
      ‖∑ n ∈ Finset.Ico 8 (T + 1), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ j * Bd := by
  intro j
  induction j with
  | zero =>
    intro T hT _
    rw [Finset.Ico_eq_empty (by omega)]; simp
  | succ j ih =>
    intro T hT hTt
    have hstep : (j : ℝ) * Bd ≤ ((j + 1 : ℕ) : ℝ) * Bd := by push_cast; nlinarith
    by_cases hlt : T < 8 * 2 ^ j
    · exact (ih T hlt hTt).trans hstep
    · push Not at hlt
      set N := 8 * 2 ^ j with hNdef
      have hN8 : 8 ≤ N := by
        have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        omega
      have hT2 : T < 2 * N := by rw [hNdef]; rw [pow_succ] at hT; omega
      have hNt : (N : ℝ) ≤ t := le_trans (by exact_mod_cast hlt) hTt
      have h1 := ih (N - 1) (by omega) (le_trans (by exact_mod_cast Nat.sub_le N 1) hNt)
      rw [show N - 1 + 1 = N by omega] at h1
      have h2 := hblk N (T + 1 - N) hN8 (by omega) hNt
      rw [show N + (T + 1 - N) = T + 1 by omega] at h2
      rw [← Finset.sum_Ico_consecutive _ hN8 (by omega : N ≤ T + 1)]
      calc _ ≤ ‖∑ n ∈ Finset.Ico 8 N, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ +
            ‖∑ n ∈ Finset.Ico N (T + 1), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ :=
            norm_add_le _ _
        _ ≤ j * Bd + Bd := add_le_add h1 h2
        _ = ((j + 1 : ℕ) : ℝ) * Bd := by push_cast; ring

/-- The first seven terms. -/
theorem head_bound (t σ : ℝ) (hσ : 0 ≤ σ) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) 8, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ 7 := by
  refine (norm_sum_le _ _).trans ?_
  have : ∀ n ∈ Finset.Ico (1 : ℕ) 8, ‖((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ 1 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn.1)
    simp; exact hσ
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- The weak Richert bound for `t ≥ t₁`. -/
theorem weak_large_t : ∃ A t₁ : ℝ, 0 ≤ A ∧ 8 ≤ t₁ ∧ ∀ σ t : ℝ, 2 / 3 ≤ σ → σ ≤ 1 → t₁ ≤ t →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      A * t ^ ((10 ^ 9 : ℝ) * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log t ^ 7 := by
  obtain ⟨K, t₀, hK, happ⟩ := approx_formula
  obtain ⟨C, hC1, hC⟩ := OAI.TwoPointCorrelations.halasz_log_dirichlet_block
  refine ⟨K + 19 + 192 * C, max t₀ 8, by positivity, le_max_right _ _,
    fun σ t hσ0 hσ1 ht => ?_⟩
  have ht0 : t₀ ≤ t := le_trans (le_max_left _ _) ht
  have ht8 : (8 : ℝ) ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := by linarith
  set L := Real.log t with hL
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le htpos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans ht8
  set E : ℝ := t ^ ((10 ^ 9 : ℝ) * (1 - σ) ^ (3 / 2 : ℝ)) with hE
  have hy0 : 0 ≤ (1 - σ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hE1 : 1 ≤ E := Real.one_le_rpow (by linarith) (by positivity)
  have hEexp : Real.exp ((10 ^ 9 : ℝ) * (1 - σ) ^ (3 / 2 : ℝ) * L) = E := by
    rw [hE, hL, Real.rpow_def_of_pos htpos]; ring_nf
  set Bd : ℝ := C * (L + 1) ^ 6 * E + 4 with hBd
  have hBd0 : 0 ≤ Bd := by positivity
  have hblk : ∀ N H : ℕ, 8 ≤ N → H ≤ N → (N : ℝ) ≤ t →
      ‖∑ n ∈ Finset.Ico N (N + H), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤ Bd := by
    intro N H hN8 hH hNt
    have := halasz_block C hC t σ (by linarith) hσ0 hσ1 N H hN8 hH hNt
    rw [hEexp] at this
    exact this
  set T := ⌊t⌋₊ with hTdef
  have hTt : (T : ℝ) ≤ t := Nat.floor_le htpos.le
  have hT8 : 8 ≤ T := Nat.le_floor (by push_cast; linarith)
  set k := Nat.log 2 T with hk
  have hpow : 2 ^ k ≤ T := Nat.pow_log_le_self 2 (by omega)
  have hpow2 : T < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) T
  have hdy := dyadic_ind t σ Bd hBd0 hblk (k + 1) T (by omega) hTt
  have hkL : (k : ℝ) ≤ 2 * L := by
    have h1 : Real.log ((2 : ℝ) ^ k) ≤ Real.log t := by
      apply Real.log_le_log (by positivity)
      have : ((2 ^ k : ℕ) : ℝ) ≤ T := by exact_mod_cast hpow
      push_cast at this
      linarith
    rw [Real.log_pow] at h1
    have h2 := Real.log_two_gt_d9
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hsplit : ∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      ∑ n ∈ Finset.Ico (1 : ℕ) 8, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) +
        ∑ n ∈ Finset.Ico 8 (T + 1), ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
    rw [Finset.sum_Ico_consecutive _ (by norm_num) (by omega)]
    congr 1
  have hsum : ‖∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ ≤
      7 + ((k + 1 : ℕ) : ℝ) * Bd := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add (head_bound t σ (by linarith)) hdy)
  have h1 := happ t ht0 σ (by linarith) hσ1
  have htri : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K + (7 + ((k + 1 : ℕ) : ℝ) * Bd) := by
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) -
            ∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ +
          ‖∑ n ∈ Finset.Icc 1 T, ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ K + (7 + ((k + 1 : ℕ) : ℝ) * Bd) := add_le_add h1 hsum
  have hL0 : 0 < L := by linarith
  have hL6 : (L + 1) ^ 6 ≤ 64 * L ^ 6 := by
    calc (L + 1) ^ 6 ≤ (2 * L) ^ 6 := by gcongr; linarith
      _ = 64 * L ^ 6 := by ring
  have hL7 : L ≤ L ^ 7 := by
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * L ^ 6 := by gcongr; exact one_le_pow₀ hL1
      _ = L ^ 7 := by ring
  have hEL : L ^ 7 ≤ E * L ^ 7 := le_mul_of_one_le_left (by positivity) hE1
  have hBd' : Bd ≤ 64 * C * L ^ 6 * E + 4 := by
    rw [hBd]
    have : C * (L + 1) ^ 6 * E ≤ C * (64 * L ^ 6) * E := by gcongr
    linarith
  have hj : ((k + 1 : ℕ) : ℝ) ≤ 3 * L := by push_cast; linarith
  have hprod : ((k + 1 : ℕ) : ℝ) * Bd ≤ 3 * L * (64 * C * L ^ 6 * E + 4) :=
    mul_le_mul hj hBd' hBd0 (by positivity)
  calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K + (7 + ((k + 1 : ℕ) : ℝ) * Bd) := htri
    _ ≤ K + 7 + 3 * L * (64 * C * L ^ 6 * E + 4) := by linarith
    _ = K + 7 + 12 * L + 192 * C * (E * L ^ 7) := by ring
    _ ≤ K * (E * L ^ 7) + 7 * (E * L ^ 7) + 12 * (E * L ^ 7) + 192 * C * (E * L ^ 7) := by
        have h1' : (1 : ℝ) ≤ E * L ^ 7 := le_trans (hL1.trans hL7) hEL
        have h2' : L ≤ E * L ^ 7 := hL7.trans hEL
        have : K ≤ K * (E * L ^ 7) := le_mul_of_one_le_right hK h1'
        linarith
    _ = (K + 19 + 192 * C) * E * L ^ 7 := by ring

/-- **Weak Richert bound**: `‖ζ(σ+it)‖ ≤ A |t|^{10⁹(1-σ)^{3/2}} log⁷|t|` for `2/3 ≤ σ ≤ 1`,
`|t| ≥ t₁`. -/
theorem weak_richert : ∃ A t₁ : ℝ, ∀ σ t : ℝ, 2 / 3 ≤ σ → σ ≤ 1 → t₁ ≤ |t| →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      A * |t| ^ ((10 ^ 9 : ℝ) * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ 7 := by
  obtain ⟨A, t₁, _, _, h⟩ := weak_large_t
  refine ⟨A, t₁, fun σ t hσ0 hσ1 ht => ?_⟩
  have hpos := h σ |t| hσ0 hσ1 ht
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at hpos ⊢; exact hpos
  · have hz : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ =
        ‖riemannZeta ((σ : ℂ) + ((|t| : ℝ) : ℂ) * I)‖ := by
      have hc : (σ : ℂ) + (t : ℂ) * I = (starRingEnd ℂ) ((σ : ℂ) + ((|t| : ℝ) : ℂ) * I) := by
        rw [abs_of_neg h0]
        apply Complex.ext <;> simp
      rw [hc, riemannZeta_conj, Complex.norm_conj]
    rw [hz]; exact hpos

end GuthMaynard.CitedZeros.VK2Rich
end

section
/-!
# The Vinogradov–Korobov zero-free region, from a weak Richert bound

`GuthMaynard.CitedZeros.VK2.vk_dev` derives `N(σ, T) = 0` for
`σ ≥ 1 - c (log T)^{-2/3} (log log T)^{-1/3}` from

* the weak Richert bound `GuthMaynard.CitedZeros.VK2Rich.weak_richert`,
  `‖ζ(σ+it)‖ ≤ A |t|^{B(1-σ)^{3/2}} log⁷|t|` for `2/3 ≤ Re s ≤ 1` and `|t| ≥ t₁` (the power of
  the logarithm does not matter for the zero-free region);
* the Landau-type lemma
  `Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg`,
  applied to `F₁(s) = ζ(1 + R(s - 1) + iγ)` and `F₂(s) = ζ(1 + R(s - 1) + 2iγ)`: rescaling the
  unit disc to radius `R = (log L / L)^{2/3}` (`L = log |γ|`) removes the normalisation
  `1 ≤ r 𝓛` of that lemma, with `𝓛 = (2B + 8) log L`;
* elementary facts proved here: a bound `‖ζ s‖ ≤ 3 + log(|Im s| + 4)` for `1 < Re s ≤ 3`,
  the lower bound `‖ζ(σ + it)‖ ≥ (σ - 1)/C`, the 3-4-1 inequality for `-ζ'/ζ` with
  `-ζ'/ζ(σ) ≤ 1/(σ - 1) + C₀`, and a zero-free neighbourhood of `Re s = 1` at bounded height.
-/

open Complex

namespace GuthMaynard.CitedZeros.VK2Aux


lemma norm_ofReal_cpow {y : ℝ} (hy : 0 < y) (w : ℂ) : ‖((y : ℂ) ^ w)‖ = y ^ w.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hy w

/-- `‖y^{-s} - n^{-s}‖ ≤ ‖s‖/n²` for `y ∈ [n, n+1]`. -/
lemma cpow_neg_sub_le {s : ℂ} (hs : 1 ≤ s.re) {n : ℝ} (hn : 1 ≤ n) {y : ℝ}
    (hy : y ∈ Set.Icc n (n + 1)) :
    ‖(y : ℂ) ^ (-s) - (n : ℂ) ^ (-s)‖ ≤ ‖s‖ / n ^ 2 := by
  have hs0 : -s ≠ 0 := by
    intro h; have : s = 0 := neg_eq_zero.mp h
    rw [this] at hs; simp at hs; linarith
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun y : ℝ => (y : ℂ) ^ (-s))
    (f' := fun y : ℝ => (-s) * (y : ℂ) ^ (-s - 1)) (a := n) (b := n + 1) (C := ‖s‖ / n ^ 2)
    (fun x hx => (hasDerivAt_ofReal_cpow_const (by linarith [hx.1]) hs0).hasDerivWithinAt)
    (fun x hx => by
      have hx0 : 0 < x := by linarith [hx.1]
      rw [norm_mul, norm_neg, norm_ofReal_cpow hx0]
      have hre : (-s - 1).re = -(s.re + 1) := by simp; ring
      rw [hre, div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      calc x ^ (-(s.re + 1)) ≤ n ^ (-(s.re + 1)) := by
            apply Real.rpow_le_rpow_of_nonpos (by linarith) hx.1 (by linarith)
        _ ≤ n ^ (-(2:ℝ)) := by
            apply Real.rpow_le_rpow_of_exponent_le hn (by linarith)
        _ = 1 / n ^ 2 := by
            rw [Real.rpow_neg (by linarith), one_div]; norm_cast) y hy
  calc _ ≤ ‖s‖ / n ^ 2 * (y - n) := key
    _ ≤ ‖s‖ / n ^ 2 * 1 := by gcongr; linarith [hy.2]
    _ = _ := mul_one _

/-- The Euler–Maclaurin-type local error: `‖n^{-s} - (n^{1-s} - (n+1)^{1-s})/(s-1)‖ ≤ ‖s‖/n²`. -/
lemma term_err_le {s : ℂ} (hs : 1 < s.re) {n : ℝ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) ^ (1 - s) - ((n + 1 : ℝ) : ℂ) ^ (1 - s)) / (s - 1)‖
      ≤ ‖s‖ / n ^ 2 := by
  have hs1 : s - 1 ≠ 0 := by
    intro h; have : s = 1 := sub_eq_zero.mp h
    rw [this] at hs; simp at hs
  have hr : -s ≠ -1 := by intro h; apply hs1; rw [neg_inj.mp h]; ring
  -- h(y) = y^{1-s}/(1-s) - n^{-s} y
  set h : ℝ → ℂ := fun y => (y : ℂ) ^ (-s + 1) / (-s + 1) - (n : ℂ) ^ (-s) * y with hh
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := h)
    (f' := fun y : ℝ => (y : ℂ) ^ (-s) - (n : ℂ) ^ (-s)) (a := n) (b := n + 1)
    (C := ‖s‖ / n ^ 2)
    (fun x hx => by
      have hx0 : x ≠ 0 := by linarith [hx.1]
      have h1 := hasDerivAt_ofReal_cpow_const' hx0 hr
      have h2 : HasDerivAt (fun y : ℝ => (n : ℂ) ^ (-s) * (y : ℂ)) ((n : ℂ) ^ (-s) * 1) x :=
        (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul _ |>.congr_deriv (by simp)
      exact (h1.sub (by simpa using h2)).hasDerivWithinAt)
    (fun x hx => cpow_neg_sub_le hs.le hn (Set.Ico_subset_Icc_self hx))
    (n + 1) ⟨by linarith, le_rfl⟩
  have eq : h (n + 1) - h n =
      -((n : ℂ) ^ (-s) - ((n : ℂ) ^ (1 - s) - ((n + 1 : ℝ) : ℂ) ^ (1 - s)) / (s - 1)) := by
    simp only [hh]
    have e1 : -s + 1 = 1 - s := by ring
    have e2 : (-s + 1) = -(s - 1) := by ring
    rw [e1]
    have hs1' : (1 - s) ≠ 0 := by intro h; apply hs1; linear_combination -h
    field_simp
    push_cast
    ring
  rw [eq, norm_neg] at key
  simpa using key

/-- Partial sums: `S M = ∑_{n=1}^{M} n^{-s}`. -/
noncomputable def S (s : ℂ) (M : ℕ) : ℂ := ∑ n ∈ Finset.range M, ((n + 1 : ℕ) : ℂ) ^ (-s)

lemma S_err {s : ℂ} (hs : 1 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ∀ k : ℕ, ‖S s (N + k) - S s N - (((N + 1 : ℕ) : ℂ) ^ (1 - s)
        - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖
      ≤ ‖s‖ * (1 / N - 1 / (N + k : ℕ)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hM : (1 : ℝ) ≤ ((N + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N + k + 1)
    have hterm := term_err_le hs hM
    have hsplit : S s (N + (k + 1)) = S s (N + k) + ((N + k + 1 : ℕ) : ℂ) ^ (-s) := by
      simp only [S, ← add_assoc, Finset.sum_range_succ]
    have heq : S s (N + (k + 1)) - S s N - (((N + 1 : ℕ) : ℂ) ^ (1 - s)
        - ((N + (k + 1) + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)
        = (S s (N + k) - S s N - (((N + 1 : ℕ) : ℂ) ^ (1 - s)
          - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
          + ((((N + k + 1 : ℕ) : ℝ) : ℂ) ^ (-s) - ((((N + k + 1 : ℕ) : ℝ) : ℂ) ^ (1 - s)
            - ((((N + k + 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ (1 - s)) / (s - 1)) := by
      rw [hsplit]
      push_cast
      ring_nf
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    have hk1 : (0 : ℝ) < ((N + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + k)
    have hbound : ‖s‖ / ((N + k + 1 : ℕ) : ℝ) ^ 2
        ≤ ‖s‖ * (1 / ((N + k : ℕ) : ℝ) - 1 / ((N + (k + 1) : ℕ) : ℝ)) := by
      have e : ((N + (k + 1) : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
      have e' : ((N + k + 1 : ℕ) : ℝ) = ((N + k : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e, e', div_eq_mul_one_div]
      gcongr
      rw [div_sub_div _ _ hk1.ne' (by linarith)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc _ ≤ ‖s‖ * (1 / N - 1 / (N + k : ℕ)) + ‖s‖ / ((N + k + 1 : ℕ) : ℝ) ^ 2 :=
          add_le_add ih hterm
      _ ≤ ‖s‖ * (1 / N - 1 / (N + k : ℕ))
          + ‖s‖ * (1 / ((N + k : ℕ) : ℝ) - 1 / ((N + (k + 1) : ℕ) : ℝ)) := by gcongr
      _ = _ := by ring

lemma norm_S_le (s : ℂ) (hs : 1 ≤ s.re) (N : ℕ) : ‖S s N‖ ≤ (harmonic N : ℝ) := by
  induction N with
  | zero => simp [S]
  | succ k ih =>
    simp only [S, Finset.sum_range_succ] at ih ⊢
    rw [harmonic_succ, Rat.cast_add]
    refine (norm_add_le _ _).trans (add_le_add ih ?_)
    have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have : ((k + 1 : ℕ) : ℂ) = (((k + 1 : ℕ) : ℝ) : ℂ) := by norm_cast
    rw [this, norm_ofReal_cpow hk, neg_re]
    calc ((k + 1 : ℕ) : ℝ) ^ (-s.re) ≤ ((k + 1 : ℕ) : ℝ) ^ (-(1:ℝ)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ k + 1))
          linarith
      _ = (((((k + 1 : ℕ) : ℚ))⁻¹ : ℚ) : ℝ) := by rw [Real.rpow_neg_one]; push_cast; ring

lemma tendsto_S {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (S s) Filter.atTop (nhds (riemannZeta s)) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) := by
    have := (Complex.summable_one_div_nat_cpow.mpr hs)
    have := (summable_nat_add_iff 1).mpr this
    simpa using this
  have := hsum.hasSum.tendsto_sum_nat
  convert this using 2 with M
  unfold S
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [cpow_neg, one_div]; push_cast; rfl

/-- Elementary bound for `ζ` just to the right of the line `Re s = 1`. -/
theorem norm_zeta_le_of_one_lt_re {s : ℂ} (hs : 1 < s.re) (hs3 : s.re ≤ 3) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 + Real.log (|s.im| + 4) := by
  have hnorm2 : 2 ≤ ‖s‖ := ht.trans (Complex.abs_im_le_norm s)
  set N : ℕ := ⌈‖s‖⌉₊ with hN
  have hNs : ‖s‖ ≤ N := Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hs1 : 2 ≤ ‖s - 1‖ := by
    refine ht.trans ((le_of_eq ?_).trans (Complex.abs_im_le_norm (s - 1)))
    simp
  -- uniform bound on the partial sums S (N + k)
  have hbound : ∀ k : ℕ, ‖S s (N + k)‖ ≤ harmonic N + 2 := by
    intro k
    have herr := S_err hs hN1 k
    have hpow : ∀ m : ℕ, 1 ≤ m → ‖((m : ℕ) : ℂ) ^ (1 - s)‖ ≤ 1 := by
      intro m hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have : ((m : ℕ) : ℂ) = ((m : ℝ) : ℂ) := by norm_cast
      rw [this, norm_ofReal_cpow hm0]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm)
      simp; linarith
    have hfrac : ‖(((N + 1 : ℕ) : ℂ) ^ (1 - s) - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ ≤ 1 := by
      rw [norm_div]
      rw [div_le_one (by linarith)]
      refine (norm_sub_le _ _).trans ?_
      have := hpow (N + 1) (by omega)
      have := hpow (N + k + 1) (by omega)
      linarith
    have hserr : ‖s‖ * (1 / N - 1 / (N + k : ℕ)) ≤ 1 := by
      have h1 : 0 ≤ 1 / ((N + k : ℕ) : ℝ) := by positivity
      have h2 : ‖s‖ * (1 / N) ≤ 1 := by
        rw [mul_one_div, div_le_one hNpos]; exact hNs
      nlinarith [norm_nonneg s]
    have hSN := norm_S_le s hs.le N
    have tri : ‖S s (N + k)‖ ≤ ‖S s (N + k) - S s N - (((N + 1 : ℕ) : ℂ) ^ (1 - s)
        - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ + ‖S s N‖
        + ‖(((N + 1 : ℕ) : ℂ) ^ (1 - s) - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)‖ := by
      have := norm_add₃_le (a := S s (N + k) - S s N - (((N + 1 : ℕ) : ℂ) ^ (1 - s)
        - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) (b := S s N)
        (c := (((N + 1 : ℕ) : ℂ) ^ (1 - s) - ((N + k + 1 : ℕ) : ℂ) ^ (1 - s)) / (s - 1))
      refine le_of_eq_of_le (congrArg norm ?_) this
      ring
    linarith
  have hlim : ‖riemannZeta s‖ ≤ harmonic N + 2 := by
    have ht' := (tendsto_S hs).comp (Filter.tendsto_add_atTop_iff_nat N |>.mpr Filter.tendsto_id)
    refine le_of_tendsto' ht'.norm (fun k => ?_)
    simpa [add_comm] using hbound k
  have hH := harmonic_le_one_add_log N
  have hNle : (N : ℝ) ≤ |s.im| + 4 := by
    have h1 : (N : ℝ) < ‖s‖ + 1 := Nat.ceil_lt_add_one (norm_nonneg _)
    have h2 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    have h3 : |s.re| ≤ 3 := abs_le.mpr ⟨by linarith, hs3⟩
    linarith
  have hlog : Real.log N ≤ Real.log (|s.im| + 4) := Real.log_le_log hNpos hNle
  linarith




/-- `ζ₀` is bounded on `[1, 2]`. -/
lemma exists_bound_zeta0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
    ‖riemannZeta₀ (x : ℂ)‖ ≤ C := by
  have hc : ContinuousOn (fun x : ℝ => ‖riemannZeta₀ (x : ℂ)‖) (Set.Icc 1 2) :=
    (differentiable_riemannZeta₀.continuous.comp continuous_ofReal).norm.continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.bddAbove
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- `ζ₁'/ζ₁` is bounded on `[1, 2]`. -/
lemma exists_bound_logDeriv_zeta1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
    ‖deriv riemannZeta₁ (x : ℂ) / riemannZeta₁ (x : ℂ)‖ ≤ C := by
  have hne : ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 → riemannZeta₁ (x : ℂ) ≠ 0 := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; simp
    · have hx1 : (x : ℂ) ≠ 1 := by
        intro h'; have := congrArg Complex.re h'; simp at this; linarith
      have := riemannZeta_eq_inv_sub_mul hx1
      intro h0
      rw [h0, mul_zero] at this
      exact riemannZeta_ne_zero_of_one_lt_re (by simpa using h) this
  have hc : ContinuousOn (fun x : ℝ => ‖deriv riemannZeta₁ (x : ℂ) / riemannZeta₁ (x : ℂ)‖)
      (Set.Icc 1 2) := by
    apply ContinuousOn.norm
    apply ContinuousOn.div
    · exact (differentiable_riemannZeta₁.deriv.continuous.comp continuous_ofReal).continuousOn
    · exact (differentiable_riemannZeta₁.continuous.comp continuous_ofReal).continuousOn
    · exact hne
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.bddAbove
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_left _ _)

/-- real part of `a / n ^ w`. -/
lemma re_ofReal_div_natCast_cpow (a : ℝ) {n : ℕ} (hn : n ≠ 0) (w : ℂ) :
    ((a : ℂ) / (n : ℂ) ^ w).re
      = a * Real.exp (-(w.re * Real.log n)) * Real.cos (w.im * Real.log n) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn', div_eq_mul_inv, ← Complex.exp_neg]
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero, add_zero,
    Real.cos_neg]
  ring_nf

/-- The 3-4-1 positivity for `L(Λ)`. -/
lemma three_four_one_vonMangoldt {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ)).re
      + 4 * (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ : ℂ) + t * I)).re
      + (LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((σ : ℂ) + 2 * t * I)).re := by
  have h0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simpa using hσ
  have S0 := (ArithmeticFunction.LSeriesSummable_vonMangoldt h0)
  have S1 := (ArithmeticFunction.LSeriesSummable_vonMangoldt h1)
  have S2 := (ArithmeticFunction.LSeriesSummable_vonMangoldt h2)
  have R0 := (Complex.hasSum_re S0.hasSum).mul_left 3
  have R1 := (Complex.hasSum_re S1.hasSum).mul_left 4
  have R2 := (Complex.hasSum_re S2.hasSum)
  have H := (R0.add R1).add R2
  unfold LSeries
  rw [← H.tsum_eq]
  refine tsum_nonneg fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.term_of_ne_zero hn]
  rw [re_ofReal_div_natCast_cpow _ hn, re_ofReal_div_natCast_cpow _ hn,
    re_ofReal_div_natCast_cpow _ hn]
  simp only [ofReal_re, ofReal_im, add_re, add_im, mul_re, mul_im, I_re, I_im, re_ofNat,
    im_ofNat]
  set a := (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-(σ * Real.log n)) with ha
  have ha0 : 0 ≤ a := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le
  set x := t * Real.log n
  have hc2 : Real.cos ((2 * t) * Real.log n) = 2 * Real.cos x ^ 2 - 1 := by
    rw [mul_assoc, Real.cos_two_mul]
  simp only [mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add]
  have : (ArithmeticFunction.vonMangoldt n : ℝ) * Real.exp (-(σ * Real.log n)) = a := rfl
  rw [this, Real.cos_zero, hc2]
  nlinarith [mul_nonneg ha0 (sq_nonneg (Real.cos x + 1))]

lemma neg_logDeriv_zeta_real {σ : ℝ} (hσ : 1 < σ) :
    -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)
      = ((σ : ℂ) - 1)⁻¹ - deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ) := by
  have hx1 : (σ : ℂ) ≠ 1 := by
    intro h'; have := congrArg Complex.re h'; simp at this; linarith
  have hsub : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hz := riemannZeta_eq_inv_sub_mul hx1
  have hd := deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hx1
  have hz1 : riemannZeta₁ (σ : ℂ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hz
    exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ) hz
  rw [hz, hd]
  field_simp
  ring

/-- The 3-4-1 inequality in the form needed. -/
theorem three_four_one_zeta : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ,
    0 ≤ 3 * (1 / (σ - 1) + C₀)
      + 4 * (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re
      + (-(deriv riemannZeta ((σ : ℂ) + 2 * t * I) / riemannZeta ((σ : ℂ) + 2 * t * I))).re := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_logDeriv_zeta1
  refine ⟨C, hC0, fun σ hσ hσ2 t => ?_⟩
  have h := three_four_one_vonMangoldt hσ t
  have h1 : 1 < ((σ : ℂ) + t * I).re := by simpa using hσ
  have h2 : 1 < ((σ : ℂ) + 2 * t * I).re := by simpa using hσ
  have h0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h0,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h2] at h
  rw [neg_logDeriv_zeta_real hσ] at h
  have hb := hC σ ⟨hσ.le, hσ2⟩
  have hre : ((((σ : ℂ) - 1)⁻¹ - deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ))).re
      ≤ 1 / (σ - 1) + C := by
    rw [sub_re]
    have e : (((σ : ℂ) - 1)⁻¹).re = 1 / (σ - 1) := by
      rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_inv, ofReal_re,
        one_div]
    rw [e]
    have := Complex.abs_re_le_norm (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ))
    linarith [neg_abs_le (deriv riemannZeta₁ (σ : ℂ) / riemannZeta₁ (σ : ℂ)).re]
  simp only [neg_div] at h ⊢
  linarith

/-- Lower bound `‖ζ(σ + it)‖ ≥ (σ - 1)/C` for `1 < σ ≤ 2`. -/
theorem zeta_lower_bound : ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ,
    (σ - 1) / C ≤ ‖riemannZeta ((σ : ℂ) + t * I)‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_zeta0
  refine ⟨1 + C, by linarith, fun σ hσ hσ2 t => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : 1 < s.re := by simp [hs, hσ]
  have h0 : 1 < ((σ : ℂ)).re := by simpa using hσ
  -- ‖L μ s‖ ≤ ‖ζ σ‖
  have hμ := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hsre
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hsre] at hμ
  have hSμ : LSeriesSummable (fun n => (ArithmeticFunction.moebius n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsre
  have hS1 : LSeriesSummable (1 : ℕ → ℂ) (σ : ℂ) := LSeriesSummable_one_iff.mpr h0
  have hnormμ : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖
      ≤ ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ := by
    refine (norm_tsum_le_tsum_norm hSμ.norm).trans ?_
    refine hSμ.norm.tsum_le_tsum (fun n => ?_) hS1.norm
    refine (LSeries.norm_term_le s (g := 1) ?_).trans ?_
    · simp only [Pi.one_apply, norm_one, Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · exact le_of_eq (by simp [LSeries.norm_term_eq, hs])
  have hreal : ∑' n, ‖LSeries.term (1 : ℕ → ℂ) (σ : ℂ) n‖ ≤ ‖riemannZeta (σ : ℂ)‖ := by
    rw [← LSeries_one_eq_riemannZeta h0]
    refine le_of_eq_of_le ?_ (Complex.re_le_norm _)
    unfold LSeries
    rw [Complex.re_tsum hS1]
    refine tsum_congr (fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [LSeries.term_of_ne_zero hn]
    have hpos : (0 : ℝ) < (n : ℝ) ^ σ := Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ
    have : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; simp
    rw [Pi.one_apply, this, ← ofReal_one, ← ofReal_div, norm_real, ofReal_re, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hzσ : ‖riemannZeta (σ : ℂ)‖ ≤ 1 / (σ - 1) + C := by
    have hx1 : (σ : ℂ) ≠ 1 := by
      intro h'; have := congrArg Complex.re h'; simp at this; linarith
    rw [riemannZeta_eq_inv_sub_add hx1]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hC σ ⟨hσ.le, hσ2⟩))
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_inv, norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith)), one_div]
  have hLμ : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ (1 + C) / (σ - 1) := by
    have : 1 / (σ - 1) + C ≤ (1 + C) / (σ - 1) := by
      rw [add_div, one_div]
      have : C ≤ C / (σ - 1) := by
        rw [le_div_iff₀ (by linarith)]; nlinarith
      linarith [show 1 / (σ - 1) = (σ - 1)⁻¹ from one_div _]
    linarith
  have hmul : ‖riemannZeta s‖ * ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ = 1 := by
    rw [← norm_mul, hμ, norm_one]
  have hpos : 0 < ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ := by
    by_contra h; rw [not_lt] at h
    have : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ = 0 :=
      le_antisymm h (norm_nonneg _)
    rw [this, mul_zero] at hmul; exact zero_ne_one hmul
  have hσ1 : 0 < σ - 1 := by linarith
  rw [div_le_iff₀ (by linarith)]
  have := mul_le_mul_of_nonneg_left hLμ (norm_nonneg (riemannZeta s))
  rw [hmul, mul_div_assoc'] at this
  rw [le_div_iff₀ hσ1] at this
  linarith

/-- No zeros near the line `Re s = 1` at bounded height. -/
theorem zero_free_bounded_height (γ₀ : ℝ) : ∃ d : ℝ, 0 < d ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
    |ρ.im| ≤ γ₀ → d ≤ 1 - ρ.re := by
  set K : Set ℂ := (fun t : ℝ => (1 : ℂ) + t * I) '' Set.Icc (-γ₀) γ₀
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  set U : Set ℂ := interior {s | riemannZeta s ≠ 0}
  have hKU : K ⊆ U := by
    rintro _ ⟨t, -, rfl⟩
    rw [mem_interior_iff_mem_nhds]
    show {s | riemannZeta s ≠ 0} ∈ nhds ((1 : ℂ) + t * I)
    by_cases ht : (1 : ℂ) + t * I = 1
    · rw [ht]; exact riemannZeta_eventually_ne_zero_nhds_one
    · have hne : riemannZeta ((1 : ℂ) + t * I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by simp)
      exact (differentiableAt_riemannZeta ht).continuousAt.eventually_ne hne
  obtain ⟨d, hd, hdU⟩ := hK.exists_cthickening_subset_open isOpen_interior hKU
  refine ⟨d, hd, fun ρ hρ hγ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  by_cases hre : 1 ≤ ρ.re
  · exact riemannZeta_ne_zero_of_one_le_re hre hρ
  rw [not_le] at hre
  have hmem : ρ ∈ Metric.cthickening d K := by
    apply Metric.mem_cthickening_of_dist_le ρ ((1 : ℂ) + ρ.im * I) d K
    · exact ⟨ρ.im, ⟨by linarith [neg_abs_le ρ.im], (le_abs_self _).trans hγ⟩, rfl⟩
    · rw [Complex.dist_eq]
      have : ρ - (1 + ρ.im * I) = ((ρ.re - 1 : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [this, norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
  exact interior_subset (hdU hmem) hρ



lemma one_le_log_of_three_le {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans ht

/-- Bound for `ζ` on the box `1 - R ≤ Re w ≤ 1 + 2R`, `X/2 ≤ |Im w| ≤ 3X`. -/
theorem zeta_bound_box (A B t₁ : ℝ)
    (hAB : ∀ σ t : ℝ, 2 / 3 ≤ σ → σ ≤ 1 → t₁ ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ 7)
    {X R : ℝ} (hX : 6 ≤ X) (hXt : 2 * t₁ ≤ X) (hL6 : 6 ≤ Real.log X)
    (hA : 128 * (|A| + 1) ≤ Real.log X)
    (hR0 : 0 < R) (hRle : R ≤ 1 / 4)
    (hR32 : R ^ (3 / 2 : ℝ) ≤ Real.log (Real.log X) / Real.log X)
    (w : ℂ) (hw1 : 1 - R ≤ w.re) (hw2 : w.re ≤ 1 + 2 * R)
    (ht1 : X / 2 ≤ |w.im|) (ht2 : |w.im| ≤ 3 * X) :
    ‖riemannZeta w‖ ≤ Real.exp ((2 * max B 0 + 8) * Real.log (Real.log X)) := by
  set L := Real.log X with hLdef
  set ℓ := Real.log L with hℓdef
  set t := |w.im| with htdef
  have hL0 : 0 < L := by linarith
  have hexpℓ : Real.exp ℓ = L := Real.exp_log hL0
  have hK : Real.exp ((2 * max B 0 + 8) * ℓ) = Real.exp (2 * max B 0 * ℓ) * L ^ 8 := by
    rw [← hexpℓ, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [hK]
  have hE1 : 1 ≤ Real.exp (2 * max B 0 * ℓ) := by
    apply Real.one_le_exp
    have : 0 ≤ ℓ := Real.log_nonneg (by linarith)
    have := le_max_right B 0
    positivity
  have ht3 : 3 ≤ t := by linarith
  have hlogt : Real.log t ≤ 2 * L := by
    have h1 : Real.log t ≤ Real.log (3 * X) := Real.log_le_log (by linarith) ht2
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h3 : Real.log 3 ≤ 3 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlogt1 : 1 ≤ Real.log t := one_le_log_of_three_le ht3
  rcases le_or_gt w.re 1 with hre | hre
  · -- Richert range
    have hw : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * I := (Complex.re_add_im w).symm
    have h := hAB w.re w.im (by linarith) hre (by linarith)
    rw [← hw] at h
    set e := B * (1 - w.re) ^ (3 / 2 : ℝ) with he
    have hy0 : 0 ≤ (1 - w.re) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    have hy : (1 - w.re) ^ (3 / 2 : ℝ) ≤ ℓ / L :=
      (Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)).trans hR32
    have he_le : e ≤ max B 0 * (ℓ / L) := by
      calc e ≤ max B 0 * (1 - w.re) ^ (3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hy0
        _ ≤ _ := mul_le_mul_of_nonneg_left hy (le_max_right _ _)
    have hP : t ^ e ≤ Real.exp (2 * max B 0 * ℓ) := by
      calc t ^ e ≤ t ^ (max B 0 * (ℓ / L)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) he_le
        _ = Real.exp (Real.log t * (max B 0 * (ℓ / L))) := Real.rpow_def_of_pos (by linarith) _
        _ ≤ Real.exp (2 * max B 0 * ℓ) := by
            apply Real.exp_le_exp.mpr
            have hBℓ : 0 ≤ max B 0 * (ℓ / L) := by
              have : 0 ≤ ℓ := Real.log_nonneg (by linarith)
              have := le_max_right B 0
              positivity
            calc Real.log t * (max B 0 * (ℓ / L)) ≤ 2 * L * (max B 0 * (ℓ / L)) :=
                  mul_le_mul_of_nonneg_right hlogt hBℓ
              _ = 2 * max B 0 * ℓ := by field_simp
    have hQ : Real.log t ^ 7 ≤ 128 * L ^ 7 := by
      calc Real.log t ^ 7 ≤ (2 * L) ^ 7 := by gcongr
        _ = 128 * L ^ 7 := by ring
    have hP0 : 0 ≤ t ^ e := Real.rpow_nonneg (by linarith) _
    have hQ0 : 0 ≤ Real.log t ^ 7 := by positivity
    calc ‖riemannZeta w‖ ≤ A * t ^ e * Real.log t ^ 7 := h
      _ ≤ |A| * t ^ e * Real.log t ^ 7 := by
          gcongr; exact le_abs_self A
      _ ≤ |A| * Real.exp (2 * max B 0 * ℓ) * (128 * L ^ 7) := by gcongr
      _ ≤ Real.exp (2 * max B 0 * ℓ) * L ^ 8 := by
          have hE0 : 0 < Real.exp (2 * max B 0 * ℓ) := Real.exp_pos _
          have h2 : |A| * (128 * L ^ 7) ≤ L ^ 8 := by
            have : 128 * |A| ≤ L := by linarith [abs_nonneg A]
            calc |A| * (128 * L ^ 7) = (128 * |A|) * L ^ 7 := by ring
              _ ≤ L * L ^ 7 := mul_le_mul_of_nonneg_right this (by positivity)
              _ = L ^ 8 := by ring
          calc |A| * Real.exp (2 * max B 0 * ℓ) * (128 * L ^ 7)
              = Real.exp (2 * max B 0 * ℓ) * (|A| * (128 * L ^ 7)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left h2 hE0.le
  · -- just right of the 1-line
    have h := norm_zeta_le_of_one_lt_re hre (by linarith) (by linarith)
    have h4 : Real.log (t + 4) ≤ Real.log 4 + L := by
      rw [← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by linarith) (by linarith)
    have hl4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have hL8 : 2 * L ≤ L ^ 8 := by
      have h1 : (1 : ℝ) ≤ L := by linarith
      calc 2 * L ≤ L * L := by nlinarith
        _ = L ^ 2 * 1 := by ring
        _ ≤ L ^ 2 * L ^ 6 := by gcongr; exact one_le_pow₀ h1
        _ = L ^ 8 := by ring
    calc ‖riemannZeta w‖ ≤ 3 + Real.log (t + 4) := h
      _ ≤ L ^ 8 := by linarith
      _ ≤ Real.exp (2 * max B 0 * ℓ) * L ^ 8 := le_mul_of_one_le_left (by positivity) hE1



/-- Facts about the radius `R = (ℓ/L)^{2/3}`. -/
lemma radius_facts {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 8) :
    0 < x ^ (2 / 3 : ℝ) ∧ x ^ (2 / 3 : ℝ) ≤ 1 / 4 ∧ (x ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = x ∧
      x ≤ x ^ (2 / 3 : ℝ) := by
  refine ⟨Real.rpow_pos_of_pos hx0 _, ?_, ?_, ?_⟩
  · calc x ^ (2 / 3 : ℝ) ≤ (1 / 8 : ℝ) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow hx0.le hx (by norm_num)
      _ = ((1 / 2 : ℝ) ^ (3 : ℝ)) ^ (2 / 3 : ℝ) := by norm_num
      _ = (1 / 2 : ℝ) ^ ((3 : ℝ) * (2 / 3)) := by rw [← Real.rpow_mul (by norm_num)]
      _ = 1 / 4 := by norm_num
  · rw [← Real.rpow_mul hx0.le]; norm_num
  · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (2 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hx0 (by linarith) (by norm_num)

/-- Core application of the Landau-type lemma at a zero of large height, after rescaling the
disc by the factor `R`. -/
theorem large_ordinate_core (A B t₁ C₂ C₀ : ℝ)
    (hAB : ∀ σ t : ℝ, 2 / 3 ≤ σ → σ ≤ 1 → t₁ ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * |t| ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * Real.log |t| ^ 7)
    (hC₂ : 0 < C₂)
    (hLB : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ, (σ - 1) / C₂ ≤ ‖riemannZeta ((σ : ℂ) + t * I)‖)
    (hC₀ : 0 ≤ C₀)
    (h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ,
      0 ≤ 3 * (1 / (σ - 1) + C₀)
        + 4 * (-(deriv riemannZeta ((σ : ℂ) + t * I) / riemannZeta ((σ : ℂ) + t * I))).re
        + (-(deriv riemannZeta ((σ : ℂ) + 2 * t * I) / riemannZeta ((σ : ℂ) + 2 * t * I))).re)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (hX : 6 ≤ |ρ.im|) (hXt : 2 * t₁ ≤ |ρ.im|) (hL6 : 6 ≤ Real.log |ρ.im|)
    (hA : 128 * (|A| + 1) ≤ Real.log |ρ.im|)
    (hC₂L : C₂ ≤ Real.log |ρ.im|)
    (hℓ1 : 1 ≤ Real.log (Real.log |ρ.im|)) (hℓC : C₀ ≤ Real.log (Real.log |ρ.im|))
    (hratio : Real.log (Real.log |ρ.im|) / Real.log |ρ.im| ≤ 1 / 8) :
    (Real.log (Real.log |ρ.im|) / Real.log |ρ.im|) ^ (2 / 3 : ℝ) /
      (20000 * ((2 * max B 0 + 8) * Real.log (Real.log |ρ.im|))) ≤ 1 - ρ.re := by
  set X := |ρ.im| with hXdef
  set L := Real.log X with hLdef
  set ℓ := Real.log L with hℓdef
  set K := 2 * max B 0 + 8 with hKdef
  set γ := ρ.im with hγdef
  have hL0 : 0 < L := by linarith
  have hx0 : 0 < ℓ / L := div_pos (by linarith) hL0
  obtain ⟨hR0, hRle, hR32, hRx⟩ := radius_facts hx0 hratio
  set R := (ℓ / L) ^ (2 / 3 : ℝ) with hRdef
  have hK3 : 3 ≤ K := by have := le_max_right B 0; linarith
  have hKℓ : 1 ≤ K * ℓ := by nlinarith
  -- the rescaled functions
  set g₁ : ℂ → ℂ := fun s => 1 + (R : ℂ) * (s - 1) + (γ : ℂ) * I with hg₁
  set g₂ : ℂ → ℂ := fun s => 1 + (R : ℂ) * (s - 1) + 2 * (γ : ℂ) * I with hg₂
  set F₁ : ℂ → ℂ := fun s => riemannZeta (g₁ s) with hF₁
  set F₂ : ℂ → ℂ := fun s => riemannZeta (g₂ s) with hF₂
  have hg₁re : ∀ s, (g₁ s).re = 1 + R * (s.re - 1) := by intro s; simp [hg₁]
  have hg₁im : ∀ s, (g₁ s).im = R * s.im + γ := by intro s; simp [hg₁]
  have hg₂re : ∀ s, (g₂ s).re = 1 + R * (s.re - 1) := by intro s; simp [hg₂]
  have hg₂im : ∀ s, (g₂ s).im = R * s.im + 2 * γ := by intro s; simp [hg₂]
  -- membership in the closed balls
  have hball : ∀ σ : ℝ, ∀ s ∈ Metric.closedBall ((σ : ℂ) + ((0 : ℝ) : ℂ) * I) 1,
      |s.re - σ| ≤ 1 ∧ |s.im| ≤ 1 := by
    intro σ s hs
    rw [Metric.mem_closedBall, Complex.dist_eq] at hs
    constructor
    · have := Complex.abs_re_le_norm (s - ((σ : ℂ) + ((0 : ℝ) : ℂ) * I))
      simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero, sub_zero,
        zero_mul, add_zero] at this
      linarith
    · have := Complex.abs_im_le_norm (s - ((σ : ℂ) + ((0 : ℝ) : ℂ) * I))
      simp only [sub_im, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, mul_one,
        add_zero, sub_zero] at this
      linarith
  have hball2 : ∀ σ : ℝ, ∀ s ∈ Metric.closedBall ((σ : ℂ) + 2 * ((0 : ℝ) : ℂ) * I) 1,
      |s.re - σ| ≤ 1 ∧ |s.im| ≤ 1 := by
    intro σ s hs
    apply hball σ s
    simpa using hs
  -- imaginary parts on the balls
  have hR_im : ∀ s : ℂ, |s.im| ≤ 1 → |R * s.im| ≤ 1 / 2 := by
    intro s hs
    rw [abs_mul, abs_of_pos hR0]
    nlinarith [abs_nonneg s.im]
  have him₁ : ∀ s : ℂ, |s.im| ≤ 1 → X / 2 ≤ |(g₁ s).im| ∧ |(g₁ s).im| ≤ 3 * X := by
    intro s hs
    have := hR_im s hs
    rw [hg₁im]
    constructor
    · have := abs_sub_abs_le_abs_sub γ (-(R * s.im))
      rw [sub_neg_eq_add, abs_neg] at this
      rw [add_comm]; linarith
    · have := abs_add_le (R * s.im) γ; linarith
  have him₂ : ∀ s : ℂ, |s.im| ≤ 1 → X / 2 ≤ |(g₂ s).im| ∧ |(g₂ s).im| ≤ 3 * X := by
    intro s hs
    have := hR_im s hs
    have h2γ : |2 * γ| = 2 * X := by rw [abs_mul]; simp [hXdef]
    rw [hg₂im]
    constructor
    · have := abs_sub_abs_le_abs_sub (2 * γ) (-(R * s.im))
      rw [sub_neg_eq_add, abs_neg, h2γ] at this
      rw [add_comm]; linarith
    · have := abs_add_le (R * s.im) (2 * γ); linarith
  have hre_box : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + 1 → ∀ s : ℂ, |s.re - σ| ≤ 1 →
      1 - R ≤ 1 + R * (s.re - 1) ∧ 1 + R * (s.re - 1) ≤ 1 + 2 * R := by
    intro σ hσ hσ2 s hs
    have := abs_le.mp hs
    constructor <;> nlinarith
  -- nonvanishing of g at ball points (avoid the pole)
  have hne₁ : ∀ s : ℂ, |s.im| ≤ 1 → g₁ s ≠ 1 := by
    intro s hs h
    have := (him₁ s hs).1
    rw [h] at this; simp at this; linarith
  have hne₂ : ∀ s : ℂ, |s.im| ≤ 1 → g₂ s ≠ 1 := by
    intro s hs h
    have := (him₂ s hs).1
    rw [h] at this; simp at this; linarith
  have hderiv_g₁ : ∀ s : ℂ, HasDerivAt g₁ (R : ℂ) s := by
    intro s
    have := (((hasDerivAt_id s).sub_const 1).const_mul (R : ℂ)).const_add 1 |>.add_const
      ((γ : ℂ) * I)
    simpa [hg₁] using this
  have hderiv_g₂ : ∀ s : ℂ, HasDerivAt g₂ (R : ℂ) s := by
    intro s
    have := (((hasDerivAt_id s).sub_const 1).const_mul (R : ℂ)).const_add 1 |>.add_const
      (2 * (γ : ℂ) * I)
    simpa [hg₂] using this
  have hanF : ∀ (g : ℂ → ℂ), (∀ s, HasDerivAt g (R : ℂ) s) → ∀ s, g s ≠ 1 →
      AnalyticAt ℂ (fun s => riemannZeta (g s)) s := by
    intro g hg s hs
    have hga : AnalyticAt ℂ g s := by
      have : Differentiable ℂ g := fun z => (hg z).differentiableAt
      exact this.analyticAt s
    exact (analyticOn_riemannZeta (g s) hs).comp hga
  have hdF : ∀ (g : ℂ → ℂ), (∀ s, HasDerivAt g (R : ℂ) s) → ∀ s, g s ≠ 1 →
      deriv (fun s => riemannZeta (g s)) s = deriv riemannZeta (g s) * R := by
    intro g hg s hs
    exact ((differentiableAt_riemannZeta hs).hasDerivAt.comp s (hg s)).deriv
  -- the real points
  have hpt : ∀ σ : ℝ, (σ : ℂ) + ((0 : ℝ) : ℂ) * I = (σ : ℂ) := by intro σ; simp
  have hpt2 : ∀ σ : ℝ, (σ : ℂ) + 2 * ((0 : ℝ) : ℂ) * I = (σ : ℂ) := by intro σ; simp
  have hg₁σ : ∀ σ : ℝ, g₁ (σ : ℂ) = ((1 + R * (σ - 1) : ℝ) : ℂ) + (γ : ℂ) * I := by
    intro σ; simp only [hg₁]; push_cast; ring
  have hg₂σ : ∀ σ : ℝ, g₂ (σ : ℂ) = ((1 + R * (σ - 1) : ℝ) : ℂ) + 2 * (γ : ℂ) * I := by
    intro σ; simp only [hg₂]; push_cast; ring
  have hσ' : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + 1 → 1 < 1 + R * (σ - 1) ∧ 1 + R * (σ - 1) ≤ 2 := by
    intro σ h1 h2
    constructor <;> nlinarith
  have hlo : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + 1 →
      (σ - 1) ^ 2 * Real.exp (-(K * ℓ)) ≤ R * (σ - 1) / C₂ := by
    intro σ h1 h2
    have hexpℓ : Real.exp ℓ = L := Real.exp_log hL0
    have hE : Real.exp (-(K * ℓ)) ≤ 1 / L ^ 2 := by
      rw [Real.exp_neg, ← one_div]
      apply one_div_le_one_div_of_le (by positivity)
      calc L ^ 2 = Real.exp (2 * ℓ) := by
            rw [← hexpℓ, ← Real.exp_nat_mul]; push_cast; ring_nf
        _ ≤ Real.exp (K * ℓ) := by
            apply Real.exp_le_exp.mpr; nlinarith
    have hRL : 1 ≤ R * L := by
      have := (div_le_iff₀ hL0).mp hRx; linarith
    have hRC : 1 / L ^ 2 ≤ R / C₂ := by
      rw [div_le_div_iff₀ (by positivity) hC₂]
      nlinarith
    have hs : (σ - 1) ^ 2 ≤ σ - 1 := by nlinarith
    calc (σ - 1) ^ 2 * Real.exp (-(K * ℓ)) ≤ (σ - 1) * (1 / L ^ 2) :=
          mul_le_mul hs hE (Real.exp_pos _).le (by linarith)
      _ ≤ (σ - 1) * (R / C₂) := mul_le_mul_of_nonneg_left hRC (by linarith)
      _ = R * (σ - 1) / C₂ := by ring
  have key := Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
    F₁ F₂ (1 - (1 - ρ.re) / R) 0 1 (K * ℓ) (R * C₀) one_pos le_rfl (by linarith)
    (mul_nonneg hR0.le hC₀)
    (by
      calc R * C₀ ≤ 1 * C₀ := mul_le_mul_of_nonneg_right (by linarith) hC₀
        _ = C₀ := one_mul _
        _ ≤ ℓ := hℓC
        _ ≤ K * ℓ := by nlinarith)
    (by
      show riemannZeta (g₁ _) = 0
      have : g₁ (((1 - (1 - ρ.re) / R : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = ρ := by
        apply Complex.ext
        · rw [hg₁re]; simp; field_simp; ring
        · rw [hg₁im]; simp [hγdef]
      rw [this, hρ])
    (by
      intro s hs
      show riemannZeta (g₁ s) ≠ 0
      apply riemannZeta_ne_zero_of_one_lt_re
      rw [hg₁re]; nlinarith)
    (by
      intro s hs
      show riemannZeta (g₂ s) ≠ 0
      apply riemannZeta_ne_zero_of_one_lt_re
      rw [hg₂re]; nlinarith)
    (by
      intro σ _ _ s hs
      exact hanF g₁ hderiv_g₁ s (hne₁ s (hball σ s hs).2))
    (by
      intro σ _ _ s hs
      exact hanF g₂ hderiv_g₂ s (hne₂ s (hball2 σ s hs).2))
    (by
      intro σ h1 h2 s hs
      obtain ⟨hb1, hb2⟩ := hball σ s hs
      obtain ⟨hr1, hr2⟩ := hre_box σ h1 h2 s hb1
      exact zeta_bound_box A B t₁ hAB hX hXt hL6 hA hR0 hRle (by rw [hR32])
        (g₁ s) (by rw [hg₁re]; exact hr1) (by rw [hg₁re]; exact hr2)
        (him₁ s hb2).1 (him₁ s hb2).2)
    (by
      intro σ h1 h2 s hs
      obtain ⟨hb1, hb2⟩ := hball2 σ s hs
      obtain ⟨hr1, hr2⟩ := hre_box σ h1 h2 s hb1
      exact zeta_bound_box A B t₁ hAB hX hXt hL6 hA hR0 hRle (by rw [hR32])
        (g₂ s) (by rw [hg₂re]; exact hr1) (by rw [hg₂re]; exact hr2)
        (him₂ s hb2).1 (him₂ s hb2).2)
    (by
      intro σ h1 h2
      rw [hpt]
      show _ ≤ ‖riemannZeta (g₁ (σ : ℂ))‖
      rw [hg₁σ]
      obtain ⟨hs1, hs2⟩ := hσ' σ h1 h2
      have := hLB _ hs1 hs2 γ
      rw [show 1 + R * (σ - 1) - 1 = R * (σ - 1) by ring] at this
      exact (hlo σ h1 h2).trans this)
    (by
      intro σ h1 h2
      rw [hpt2]
      show _ ≤ ‖riemannZeta (g₂ (σ : ℂ))‖
      rw [hg₂σ]
      obtain ⟨hs1, hs2⟩ := hσ' σ h1 h2
      have := hLB _ hs1 hs2 (2 * γ)
      rw [show 1 + R * (σ - 1) - 1 = R * (σ - 1) by ring] at this
      rw [show ((2 * γ : ℝ) : ℂ) = 2 * (γ : ℂ) by push_cast; ring] at this
      exact (hlo σ h1 h2).trans this)
    (by
      intro σ h1 h2
      rw [hpt, hpt2]
      have hσ1 : (σ : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      have hb : |((σ : ℂ)).im| ≤ 1 := by simp
      have e1 : deriv F₁ (σ : ℂ) = deriv riemannZeta (g₁ σ) * R :=
        hdF g₁ hderiv_g₁ _ (hne₁ _ hb)
      have e2 : deriv F₂ (σ : ℂ) = deriv riemannZeta (g₂ σ) * R :=
        hdF g₂ hderiv_g₂ _ (hne₂ _ hb)
      have e1' : F₁ (σ : ℂ) = riemannZeta (g₁ σ) := rfl
      have e2' : F₂ (σ : ℂ) = riemannZeta (g₂ σ) := rfl
      rw [e1, e2, e1', e2', hg₁σ, hg₂σ]
      obtain ⟨hs1, hs2⟩ := hσ' σ h1 h2
      have h := mul_nonneg hR0.le (h341 _ hs1 hs2 γ)
      have e3 : R * (1 / (1 + R * (σ - 1) - 1)) = 1 / (σ - 1) := by
        rw [show 1 + R * (σ - 1) - 1 = R * (σ - 1) by ring]
        have : σ - 1 ≠ 0 := by linarith
        field_simp
      have r1 : ∀ a b : ℂ, (-(a * (R : ℂ) / b)).re = R * (-(a / b)).re := by
        intro a b
        rw [show -(a * (R : ℂ) / b) = (R : ℂ) * (-(a / b)) by ring, re_ofReal_mul]
      rw [r1, r1]
      set σ' := 1 + R * (σ - 1)
      have : R * (3 * (1 / (σ' - 1) + C₀)
          + 4 * (-(deriv riemannZeta ((σ' : ℂ) + γ * I) / riemannZeta ((σ' : ℂ) + γ * I))).re
          + (-(deriv riemannZeta ((σ' : ℂ) + 2 * γ * I)
              / riemannZeta ((σ' : ℂ) + 2 * γ * I))).re)
          = 3 * (1 / (σ - 1) + R * C₀)
            + 4 * (R * (-(deriv riemannZeta ((σ' : ℂ) + γ * I)
                / riemannZeta ((σ' : ℂ) + γ * I))).re)
            + R * (-(deriv riemannZeta ((σ' : ℂ) + 2 * γ * I)
                / riemannZeta ((σ' : ℂ) + 2 * γ * I))).re := by
        rw [← e3]; ring
      linarith)
  rw [sub_sub_cancel, le_div_iff₀ hR0] at key
  calc R / (20000 * (K * ℓ)) = 1 / (20000 * (K * ℓ)) * R := by ring
    _ ≤ 1 - ρ.re := key


end GuthMaynard.CitedZeros.VK2Aux

namespace GuthMaynard.CitedZeros.VK2

open VK2Aux

/-- Zeros of large height: `1 - β ≥ c₁ (log |γ|)^{-2/3} (log log |γ|)^{-1/3}`. -/
theorem large_ordinates : ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 →
    X₀ ≤ |ρ.im| →
      c₁ * Real.log |ρ.im| ^ (-(2 / 3) : ℝ) * Real.log (Real.log |ρ.im|) ^ (-(1 / 3) : ℝ)
        ≤ 1 - ρ.re := by
  obtain ⟨A, t₁, hAB⟩ := GuthMaynard.CitedZeros.VK2Rich.weak_richert
  set B : ℝ := 10 ^ 9 with hBdef
  obtain ⟨C₂, hC₂, hLB⟩ := zeta_lower_bound
  obtain ⟨C₀, hC₀, h341⟩ := three_four_one_zeta
  set K := 2 * max B 0 + 8 with hK
  have hK3 : 3 ≤ K := by have := le_max_right B 0; linarith
  set M := max (max (max (max 256 (128 * (|A| + 1))) C₂) (Real.exp (max 1 C₀))) (2 * t₁) with hM
  refine ⟨1 / (20000 * K), by positivity, Real.exp M, Real.exp_pos _, fun ρ hρ hX => ?_⟩
  set X := |ρ.im| with hXdef
  set L := Real.log X with hLdef
  set ℓ := Real.log L with hℓdef
  have hLM : M ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith [Real.exp_pos M])]; exact hX
  have hL256 : 256 ≤ L := le_trans (by simp [hM]) hLM
  have hLA : 128 * (|A| + 1) ≤ L := le_trans (by simp [hM]) hLM
  have hLC : C₂ ≤ L := le_trans (by simp [hM]) hLM
  have hLE : Real.exp (max 1 C₀) ≤ L := le_trans (by simp [hM]) hLM
  have hL0 : 0 < L := by linarith
  have hℓmax : max 1 C₀ ≤ ℓ := by
    rw [hℓdef, Real.le_log_iff_exp_le hL0]; exact hLE
  have hℓ1 : 1 ≤ ℓ := le_trans (le_max_left _ _) hℓmax
  have hℓC : C₀ ≤ ℓ := le_trans (le_max_right _ _) hℓmax
  have hX6 : 6 ≤ X := by
    have h1 : M + 1 ≤ Real.exp M := Real.add_one_le_exp M
    have h2 : 256 ≤ M := by simp [hM]
    linarith
  have hXt : 2 * t₁ ≤ X := by
    have h1 : M + 1 ≤ Real.exp M := Real.add_one_le_exp M
    have h2 : 2 * t₁ ≤ M := le_max_right _ _
    linarith
  have hratio : ℓ / L ≤ 1 / 8 := by
    have h1 : ℓ ≤ L ^ (1 / 2 : ℝ) / (1 / 2) := Real.log_le_rpow_div hL0.le (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h1
    have hs : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
    have hs16 : 16 ≤ Real.sqrt L := by
      rw [show (16 : ℝ) = Real.sqrt 256 by
        rw [show (256 : ℝ) = 16 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hL256
    rw [div_le_iff₀ hL0]
    nlinarith
  have core := large_ordinate_core A B t₁ C₂ C₀ hAB hC₂ hLB hC₀ h341 ρ hρ hX6 hXt (by linarith) hLA
    hLC hℓ1 hℓC hratio
  rw [← hXdef, ← hLdef, ← hℓdef] at core
  refine le_of_eq_of_le ?_ core
  have hℓ0 : 0 < ℓ := by linarith
  rw [Real.div_rpow hℓ0.le hL0.le, Real.rpow_neg hL0.le, Real.rpow_neg hℓ0.le]
  have h13 : ℓ ^ (1 / 3 : ℝ) * ℓ ^ (2 / 3 : ℝ) = ℓ := by
    rw [← Real.rpow_add hℓ0]; norm_num
  have hp1 : 0 < ℓ ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hℓ0 _
  have hp2 : 0 < L ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hL0 _
  field_simp
  rw [mul_assoc, h13]

/-- **Vinogradov–Korobov zero-free region** (from the weak Richert bound). -/
theorem vk_dev :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ σ →
      LindelofHypothesis.zeroDensityCount σ T = 0 := by
  obtain ⟨c₁, hc₁, X₀, hX₀, hlarge⟩ := large_ordinates
  obtain ⟨d, hd, hsmall⟩ := zero_free_bounded_height (max X₀ (Real.exp (Real.exp 1)))
  refine ⟨min c₁ d / 2, by positivity, max X₀ (Real.exp (Real.exp 1)), fun T hT σ hσ => ?_⟩
  have hTe : Real.exp (Real.exp 1) ≤ T := le_trans (le_max_right _ _) hT
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTe
  have hlogT : Real.exp 1 ≤ Real.log T := by rw [Real.le_log_iff_exp_le hT0]; exact hTe
  have hlogT0 : 0 < Real.log T := lt_of_lt_of_le (Real.exp_pos _) hlogT
  have hllT : 1 ≤ Real.log (Real.log T) := by rw [Real.le_log_iff_exp_le hlogT0]; exact hlogT
  have hllT0 : 0 < Real.log (Real.log T) := by linarith
  set f := Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) with hf
  have hf0 : 0 < f := by positivity
  have hf1 : f ≤ 1 := by
    have h1 : Real.log T ^ (-(2 / 3) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.add_one_le_exp (1 : ℝ)])
        (by norm_num)
    have h2 : Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hllT (by norm_num)
    calc f ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 1 := one_mul 1
  have hσ' : 1 - min c₁ d / 2 * f ≤ σ := by rw [hf, ← mul_assoc]; exact hσ
  have hnone : ∀ s : ℂ, ¬ (riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T) := by
    rintro s ⟨hs, hsσ, hsT⟩
    have hmin1 : min c₁ d ≤ c₁ := min_le_left _ _
    have hmin2 : min c₁ d ≤ d := min_le_right _ _
    have hminpos : 0 < min c₁ d := lt_min hc₁ hd
    rcases le_or_gt (max X₀ (Real.exp (Real.exp 1))) |s.im| with hbig | hsmall'
    · have h := hlarge s hs (le_trans (le_max_left _ _) hbig)
      have hbig' : Real.exp (Real.exp 1) ≤ |s.im| := le_trans (le_max_right _ _) hbig
      have hX0 : 0 < |s.im| := lt_of_lt_of_le (Real.exp_pos _) hbig'
      have hL1 : Real.log |s.im| ≤ Real.log T := Real.log_le_log hX0 hsT
      have hLe : Real.exp 1 ≤ Real.log |s.im| := by
        rw [Real.le_log_iff_exp_le hX0]; exact hbig'
      have hLpos : 0 < Real.log |s.im| := lt_of_lt_of_le (Real.exp_pos _) hLe
      have hℓ1 : 1 ≤ Real.log (Real.log |s.im|) := by
        rw [Real.le_log_iff_exp_le hLpos]; exact hLe
      have hℓpos : 0 < Real.log (Real.log |s.im|) := by linarith
      have hℓT : Real.log (Real.log |s.im|) ≤ Real.log (Real.log T) :=
        Real.log_le_log hLpos hL1
      have m1 : Real.log T ^ (-(2 / 3) : ℝ) ≤ Real.log |s.im| ^ (-(2 / 3) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hLpos hL1 (by norm_num)
      have m2 : Real.log (Real.log T) ^ (-(1 / 3) : ℝ)
          ≤ Real.log (Real.log |s.im|) ^ (-(1 / 3) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hℓpos hℓT (by norm_num)
      have hfle : f ≤ Real.log |s.im| ^ (-(2 / 3) : ℝ)
          * Real.log (Real.log |s.im|) ^ (-(1 / 3) : ℝ) :=
        mul_le_mul m1 m2 (by positivity) (by positivity)
      have : c₁ * f ≤ 1 - s.re := by
        calc c₁ * f ≤ c₁ * (Real.log |s.im| ^ (-(2 / 3) : ℝ)
              * Real.log (Real.log |s.im|) ^ (-(1 / 3) : ℝ)) :=
              mul_le_mul_of_nonneg_left hfle hc₁.le
          _ = _ := by ring
          _ ≤ 1 - s.re := h
      have : min c₁ d / 2 * f < c₁ * f := by
        apply mul_lt_mul_of_pos_right _ hf0; linarith
      linarith
    · have h := hsmall s hs hsmall'.le
      have : min c₁ d / 2 * f ≤ d / 2 := by
        calc min c₁ d / 2 * f ≤ min c₁ d / 2 * 1 := by gcongr
          _ ≤ d / 2 := by linarith
      linarith
  unfold LindelofHypothesis.zeroDensityCount
  have : IsEmpty {s : ℂ | riemannZeta s = 0 ∧ σ ≤ s.re ∧ |s.im| ≤ T} :=
    ⟨fun ⟨s, hs⟩ => hnone s hs⟩
  exact tsum_empty

end GuthMaynard.CitedZeros.VK2
end

theorem solution :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ σ : ℝ,
      1 - c * Real.log T ^ (-(2 / 3) : ℝ) * Real.log (Real.log T) ^ (-(1 / 3) : ℝ) ≤ σ →
      LindelofHypothesis.zeroDensityCount σ T = 0 :=
  GuthMaynard.CitedZeros.VK2.vk_dev
