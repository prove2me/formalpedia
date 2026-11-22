-- Prove2me | solution 1 for MasulloRH.unit_height_em_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T12:48:19.0419+00:00
-- url     : https://prove2.me/submissions/e3bc0f46-0458-46f3-9bd7-2ce1dc824cfa

import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Theorems.Thm_ZetaReflection_EMHigh_em_zeta_orderK_enclosure_odd
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

open scoped Real Nat

namespace MasulloRH

private lemma norm_poch_le_pow {s : ℂ} {B : ℝ} (hB : ‖s‖ ≤ B) (M : ℕ) :
    ∀ j : ℕ, j ≤ M + 1 →
      ‖ZetaReflection.EMHigh.poch s j‖ ≤ (B + (M : ℝ)) ^ j := by
  intro j
  induction j with
  | zero =>
    intro _
    simp [ZetaReflection.EMHigh.poch]
  | succ j ih =>
    intro hj
    have hjM : j ≤ M := Nat.le_of_succ_le_succ hj
    have hj_le : j ≤ M + 1 := Nat.le_trans hjM (Nat.le_succ M)
    have h_ih : ‖ZetaReflection.EMHigh.poch s j‖ ≤ (B + (M : ℝ)) ^ j := ih hj_le
    have h_step : ‖s + (j : ℂ)‖ ≤ B + (M : ℝ) := by
      have h1 : ‖s + (j : ℂ)‖ ≤ ‖s‖ + ‖(j : ℂ)‖ := norm_add_le s (j : ℂ)
      have h2 : ‖(j : ℂ)‖ = (j : ℝ) := Complex.norm_natCast j
      have h3 : (j : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr hjM
      linarith
    have hBM_nonneg : 0 ≤ B + (M : ℝ) := by
      have : 0 ≤ ‖s‖ := norm_nonneg s
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    calc
      ‖ZetaReflection.EMHigh.poch s (j + 1)‖
          = ‖ZetaReflection.EMHigh.poch s j * (s + (j : ℂ))‖ := rfl
      _ = ‖ZetaReflection.EMHigh.poch s j‖ * ‖s + (j : ℂ)‖ := norm_mul _ _
      _ ≤ (B + (M : ℝ)) ^ j * (B + (M : ℝ)) :=
            mul_le_mul h_ih h_step (norm_nonneg _) (pow_nonneg hBM_nonneg j)
      _ = (B + (M : ℝ)) ^ (j + 1) := by ring

theorem unit_height_em_enclosure_aux (n k K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
      ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤
        ((((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K)) : ℚ) : ℝ) := by
  intro margin left bottom top s hs
  rcases Complex.mem_reProdIm.mp hs with ⟨⟨hre_lo, hre_hi⟩, ⟨him_lo, him_hi⟩⟩
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmargin_pos : 0 < margin := by
    dsimp [margin]
    positivity
  have hre_gt_half : 1 / 2 < s.re := by
    dsimp [left] at hre_lo
    linarith
  have hre_pos : 0 < s.re := by linarith
  have him_gt : (100000 : ℝ) + (n : ℝ) < s.im := by
    dsimp [bottom] at him_lo
    linarith
  have him_le : s.im ≤ (100001 : ℝ) + (n : ℝ) := by
    dsimp [top] at him_hi
    linarith
  have hs1 : s ≠ 1 := by
    intro h_eq
    have : s.im = 0 := by simpa using congrArg Complex.im h_eq
    linarith
  have hnorm_s : ‖s‖ ≤ (100002 : ℝ) + (n : ℝ) := by
    have h1 : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    have h2 : |s.re| = s.re := abs_of_pos hre_pos
    have h3 : |s.im| = s.im := abs_of_pos (by linarith)
    linarith
  have hpoch :
      ‖ZetaReflection.EMHigh.poch s (2 * K + 1)‖ ≤
        ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) := by
    have hraw := norm_poch_le_pow hnorm_s (2 * K) (2 * K + 1) (le_refl _)
    have hcast : (100002 : ℝ) + (n : ℝ) + ((2 * K : ℕ) : ℝ) = ((100002 + n + 2 * K : ℕ) : ℝ) := by
      push_cast
      ring
    rwa [hcast] at hraw
  have hem :=
    ZetaReflection.EMHigh.em_zeta_orderK_enclosure_odd K hK hre_pos hs1 hN
  have hpi_gt : (3 : ℝ) < π := Real.pi_gt_three
  have hpi_lt : π < (4 : ℝ) := Real.pi_lt_four
  have hpow2_ge : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * K - 1) := by
    have h2K1 : 1 ≤ 2 * K - 1 := by omega
    calc
      (2 : ℝ) = (2 : ℝ) ^ (1 : ℕ) := by ring
      _ ≤ (2 : ℝ) ^ (2 * K - 1) := pow_le_pow_right₀ (by norm_num) h2K1
  have hnum_le : 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) ≤ 4 := by
    have hpi2_le : π ^ 2 / 6 - 1 ≤ 2 := by nlinarith
    have hpi2_nonneg : 0 ≤ π ^ 2 / 6 - 1 := by nlinarith
    have hdiv_le : (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1) ≤ 1 := by
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (2 * K - 1) := by positivity
      rw [div_le_iff₀ hpow_pos]
      linarith
    linarith
  have hnum_nonneg : 0 ≤ 2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) := by
    have hpi2_nonneg : 0 ≤ π ^ 2 / 6 - 1 := by nlinarith
    positivity
  have h2pi_pow : (6 : ℝ) ^ (2 * K + 1) ≤ (2 * π) ^ (2 * K + 1) :=
    pow_le_pow_left₀ (by norm_num) (by linarith) (2 * K + 1)
  have hprefactor :
      2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) ≤
        4 / (6 : ℝ) ^ (2 * K + 1) := by
    calc
      2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1)
          ≤ 4 / (2 * π) ^ (2 * K + 1) :=
            div_le_div_of_nonneg_right hnum_le (by positivity)
      _ ≤ 4 / (6 : ℝ) ^ (2 * K + 1) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) h2pi_pow
  have hdenom_ge : (2 : ℝ) ≤ s.re + ((2 * K + 1 : ℕ) : ℝ) - 1 := by
    have h2K_cast : (3 : ℝ) ≤ ((2 * K + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 3 ≤ 2 * K + 1 by omega)
    linarith
  have hN_pow :
      (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤ 1 / (N : ℝ) ^ (2 * K) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := Nat.one_le_cast.mpr hN
    have hexp : -(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤ -((2 * K : ℕ) : ℝ) := by
      have : ((2 * K + 1 : ℕ) : ℝ) = ((2 * K : ℕ) : ℝ) + 1 := by push_cast; ring
      linarith
    calc
      (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1))
          ≤ (N : ℝ) ^ (-((2 * K : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
      _ = ((N : ℝ) ^ ((2 * K : ℕ) : ℝ))⁻¹ := Real.rpow_neg (Nat.cast_nonneg N) _
      _ = 1 / (N : ℝ) ^ (2 * K) := by
            rw [Real.rpow_natCast, one_div]
  have h_combine :
      2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) *
          ‖ZetaReflection.EMHigh.poch s (2 * K + 1)‖ *
          (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) /
          (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤
        ((((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K)) : ℚ) : ℝ) := by
    have h1 :
        2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) *
            ‖ZetaReflection.EMHigh.poch s (2 * K + 1)‖ ≤
          (4 / (6 : ℝ) ^ (2 * K + 1)) * ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) :=
      mul_le_mul hprefactor hpoch (norm_nonneg _) (by positivity)
    have h2 :
        2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) *
            ‖ZetaReflection.EMHigh.poch s (2 * K + 1)‖ *
            (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) ≤
          (4 / (6 : ℝ) ^ (2 * K + 1)) * ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) *
            (1 / (N : ℝ) ^ (2 * K)) :=
      mul_le_mul h1 hN_pow (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by positivity)
    have h3 :
        2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) *
            ‖ZetaReflection.EMHigh.poch s (2 * K + 1)‖ *
            (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) /
            (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) ≤
          (4 / (6 : ℝ) ^ (2 * K + 1)) * ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) *
            (1 / (N : ℝ) ^ (2 * K)) / 2 := by
      calc
        2 * (1 + (π ^ 2 / 6 - 1) / 2 ^ (2 * K - 1)) / (2 * π) ^ (2 * K + 1) *
              ‖ZetaReflection.EMHigh.poch s (2 * K + 1)‖ *
              (N : ℝ) ^ (-(s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)) /
              (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1)
            ≤ (4 / (6 : ℝ) ^ (2 * K + 1)) * ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) *
                (1 / (N : ℝ) ^ (2 * K)) / (s.re + ((2 * K + 1 : ℕ) : ℝ) - 1) :=
              div_le_div_of_nonneg_right h2 (by linarith)
        _ ≤ (4 / (6 : ℝ) ^ (2 * K + 1)) * ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) *
              (1 / (N : ℝ) ^ (2 * K)) / 2 :=
              div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom_ge
    have h_eq :
        (4 / (6 : ℝ) ^ (2 * K + 1)) * ((100002 + n + 2 * K : ℕ) : ℝ) ^ (2 * K + 1) *
            (1 / (N : ℝ) ^ (2 * K)) / 2 =
          ((((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
            (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K)) : ℚ) : ℝ) := by
      push_cast
      rw [pow_succ (6 : ℝ) (2 * K)]
      ring
    linarith
  exact le_trans hem h_combine

end MasulloRH

theorem solution (n k K N : ℕ) (hK : 1 ≤ K) (hN : 1 ≤ N) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let left : ℝ := 1 / 2 + margin
    let bottom : ℝ := (100000 : ℝ) + n + margin
    let top : ℝ := (100000 : ℝ) + n + 1
    ∀ s ∈ Complex.reProdIm (Set.Icc left 1) (Set.Icc bottom top),
      ‖riemannZeta s - ZetaReflection.EMHigh.emFinite K s N‖ ≤
        ((((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K)) : ℚ) : ℝ) :=
  MasulloRH.unit_height_em_enclosure_aux n k K N hK hN
