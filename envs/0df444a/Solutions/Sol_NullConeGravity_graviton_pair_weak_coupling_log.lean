-- Prove2me | solution 1 for NullConeGravity.graviton_pair_weak_coupling_log
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T19:58:23.227293+00:00
-- url     : https://prove2.me/submissions/4be83fa0-542d-47d5-9c62-1b7d10ccd008

import Definitions.Def_NullConeGravity_pairRadialData
import Theorems.Thm_NullConeGravity_graviton_pair_cutoff_error
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

open NullConeGravity Filter
open scoped Topology

/-- The scaled imaginary part of a retained mode differs from its linear sine term by at most 1/s. -/
private lemma mode_error (s : ℝ) (hs : 0 < s) (k : ℕ) (hk : (k : ℝ) + 1 ≤ s) :
    |s ^ 3 * (pairTerm s k).im + 1 / (k + 1 : ℝ)| ≤ 1 / s := by
  let n : ℝ := k + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hphase : (Complex.exp (-2 * Complex.I * (k + 1 : ℂ) / (s : ℂ))).im =
      -Real.sin (2 * n / s) := by
    rw [Complex.exp_im, Complex.div_ofReal_re, Complex.div_ofReal_im]
    dsimp [n]
    norm_num [Complex.mul_re, Complex.mul_im, neg_mul, neg_div]
  have hreal : 2 * (radialVar s k : ℂ) ^ 2 = ((2 * (radialVar s k) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hterm : s ^ 3 * (pairTerm s k).im + 1 / n =
      (s / (2 * n ^ 2)) * (2 * n / s - Real.sin (2 * n / s)) := by
    rw [pairTerm, hreal, Complex.im_ofReal_mul, hphase]
    change s ^ 3 * (2 * (1 / (2 * s * n)) ^ 2 * _) + 1 / n = _
    field_simp
    ring
  change |s ^ 3 * (pairTerm s k).im + 1 / n| ≤ 1 / s
  rw [hterm, abs_mul, abs_of_pos (by positivity : 0 < s / (2 * n ^ 2))]
  calc
    _ ≤ (s / (2 * n ^ 2)) * (|2 * n / s| ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le _) (by positivity)
    _ = 2 * n / (3 * s ^ 2) := by
      rw [abs_of_pos (by positivity)]
      field_simp
      ring
    _ ≤ 1 / s := by
      apply (div_le_div_iff₀ (by positivity) hs).mpr
      have hns : n * s ≤ s * s := mul_le_mul_of_nonneg_right hk hs.le
      nlinarith

private lemma finite_error (s : ℝ) (hs : 0 < s) (N : ℕ) (hN : (N : ℝ) ≤ s) :
    |s ^ 3 * (∑ k ∈ Finset.range N, pairTerm s k).im + (harmonic N : ℝ)| ≤ 1 := by
  have hsum : (∑ k ∈ Finset.range N, (1 : ℝ) / (k + 1)) = (harmonic N : ℝ) := by
    simp [harmonic, Rat.cast_sum, one_div]
  rw [← hsum, Complex.im_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, (1 : ℝ) / s := by
      apply Finset.sum_le_sum
      intro k hk
      have hsucc : k + 1 ≤ N := Finset.mem_range.mp hk
      exact mode_error s hs k ((by exact_mod_cast hsucc : (k : ℝ) + 1 ≤ (N : ℝ)).trans hN)
    _ = (N : ℝ) / s := by simp [nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hs).mpr hN

/-- Split the full amplitude at the natural floor of s. Only the harmonic sum grows. -/
private lemma bounded_log_error (s : ℝ) (hs : 2 ≤ s) :
    |s ^ 3 * (pairAmplitude s).im + Real.log s| ≤ 3 := by
  let N := ⌊s⌋₊
  let S := ∑ k ∈ Finset.range N, pairTerm s k
  have hspos : 0 < s := by linarith
  have hN : 1 ≤ N := Nat.floor_pos.mpr (by linarith)
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlow : |s ^ 3 * S.im + (harmonic N : ℝ)| ≤ 1 :=
    finite_error s hspos N (Nat.floor_le hspos.le)
  have htail : |s ^ 3 * ((pairAmplitude s).im - S.im)| ≤ 1 := by
    have him : |(pairAmplitude s).im - S.im| ≤ ‖pairAmplitude s - S‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (pairAmplitude s - S)
    rw [abs_mul, abs_of_pos (pow_pos hspos 3)]
    calc
      _ ≤ s ^ 3 * (1 / (2 * s ^ 2 * (N : ℝ))) := mul_le_mul_of_nonneg_left
        (him.trans (graviton_pair_cutoff_error s hspos N hN)) (by positivity)
      _ = s / (2 * (N : ℝ)) := by field_simp
      _ ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have hfloor : s < (N : ℝ) + 1 := Nat.lt_floor_add_one s
        linarith
  have hlog : |Real.log s - (harmonic N : ℝ)| ≤ 1 := by
    have h₁ := log_le_harmonic_floor s hspos.le
    have h₂ := harmonic_floor_le_one_add_log s (by linarith)
    change |Real.log s - (harmonic ⌊s⌋₊ : ℝ)| ≤ 1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ = |s ^ 3 * ((pairAmplitude s).im - S.im) + (s ^ 3 * S.im + (harmonic N : ℝ)) +
            (Real.log s - (harmonic N : ℝ))| := by congr 1; ring
    _ ≤ (|s ^ 3 * ((pairAmplitude s).im - S.im)| + |s ^ 3 * S.im + (harmonic N : ℝ)|) +
            |Real.log s - (harmonic N : ℝ)| :=
      (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
    _ ≤ 3 := by linarith

theorem solution :
    Tendsto (fun s : ℝ => s ^ 3 * (pairAmplitude s).im / Real.log s)
      atTop (𝓝 (-1 : ℝ)) := by
  have hzero : Tendsto (fun s : ℝ => (s ^ 3 * (pairAmplitude s).im + Real.log s) / Real.log s)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_const_nhds (x := (3 : ℝ))).div_atTop Real.tendsto_log_atTop)
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
    have hpos : 0 < Real.log s := Real.log_pos (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right (bounded_log_error s hs) hpos.le
  have hlim : Tendsto (fun s : ℝ => (s ^ 3 * (pairAmplitude s).im + Real.log s) / Real.log s - 1)
      atTop (𝓝 (-1 : ℝ)) := by simpa only [zero_sub] using hzero.sub_const 1
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with s hs
  have hpos : 0 < Real.log s := Real.log_pos (by linarith)
  field_simp
  ring
