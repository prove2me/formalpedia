-- Prove2me | solution 1 for LinParamBandits.UEGeneral.radius_large_deviation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:56:38.738494+00:00
-- url     : https://prove2.me/submissions/0f4141b3-d0aa-4448-804a-ee658566bd7d

import Mathlib
import Definitions.Def_LinParamBandits_UEGeneral_Model
import Definitions.Def_LinParamBandits_UEGeneral_UEPolicy
import Theorems.Thm_LinParamBandits_UEGeneral_chernoff_finite_arms
import Theorems.Thm_LinParamBandits_UEGeneral_chernoff_infinite_arms

open MeasureTheory ProbabilityTheory

namespace UEGenB6Aux

open LinParamBandits.UEGeneral

lemma kappa0_ge_two (ubar lam0 : ℝ) (hlam0 : 0 < lam0) : 2 ≤ kappa0 ubar lam0 := by
  unfold kappa0
  have h1 : 0 ≤ Real.log (1 + 36 * ubar ^ 2 / lam0) := Real.log_nonneg (by
    have : 0 ≤ 36 * ubar ^ 2 / lam0 := by positivity
    linarith)
  have h2 : 1 ≤ Real.sqrt (1 + Real.log (1 + 36 * ubar ^ 2 / lam0)) := by
    rw [Real.one_le_sqrt]; linarith
  linarith

lemma pow_eq_exp (t : ℝ) (ht : 0 < t) (n : ℕ) : t ^ n = Real.exp (n * Real.log t) := by
  rw [← Real.log_pow, Real.exp_log (by positivity)]

/-- Numerical bound in the finite case: `t^{5n} e^{-ζ²/2} ≤ 1/t²` for `ζ² = 16 κ₀⁴ n log t`. -/
lemma finite_num (t : ℕ) (ht : 2 ≤ t) (n : ℕ) (hn : 1 ≤ n) (κ : ℝ) (hκ : 2 ≤ κ) :
    (t : ℝ) ^ (5 * n) * Real.exp (-(4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt n) ^ 2 / 2) ≤
      1 / (t : ℝ) ^ 2 := by
  have htp : (0 : ℝ) < t := by positivity
  have hL : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hsq : (4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt n) ^ 2 = 16 * κ ^ 4 * Real.log t * n := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hL, Real.sq_sqrt (by positivity)]; ring
  rw [hsq, pow_eq_exp _ htp (5 * n), one_div, pow_eq_exp _ htp 2,
    ← Real.exp_neg, ← Real.exp_add, Real.exp_le_exp]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hκ4 : 16 ≤ κ ^ 4 := by nlinarith [sq_nonneg (κ ^ 2 - 4), sq_nonneg κ]
  push_cast
  have : (5 * n - 8 * κ ^ 4 * n : ℝ) ≤ -2 := by nlinarith
  nlinarith

/-- Numerical bound in the infinite case: `t^{rκ₀²} e^{-ζ²/4} ≤ 1/t²` for `ζ² = 16 κ₀² r log t`. -/
lemma infinite_num (t : ℕ) (ht : 2 ≤ t) (r : ℕ) (hr : 1 ≤ r) (κ : ℝ) (hκ : 2 ≤ κ) :
    (t : ℝ) ^ ((r : ℝ) * κ ^ 2) *
        Real.exp (-(4 * κ * Real.sqrt ((r : ℝ) * Real.log t)) ^ 2 / 4) ≤ 1 / (t : ℝ) ^ 2 := by
  have htp : (0 : ℝ) < t := by positivity
  have hL : 0 ≤ Real.log t := Real.log_natCast_nonneg t
  have hsq : (4 * κ * Real.sqrt ((r : ℝ) * Real.log t)) ^ 2 = 16 * κ ^ 2 * (r * Real.log t) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [hsq, Real.rpow_def_of_pos htp, one_div, pow_eq_exp _ htp 2, ← Real.exp_neg, ← Real.exp_add,
    Real.exp_le_exp]
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have : (2 : ℝ) ≤ 3 * r * κ ^ 2 := by nlinarith
  push_cast
  nlinarith

/-- The common case analysis of Lemma B.6. -/
lemma core {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰n : 𝒰.Nonempty)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (σ₀ ubar lam0 : ℝ) (hσ₀ : 0 < σ₀)
    (hlam0 : 0 < lam0) (t : ℕ) (ht : r ≤ t) (W I : Ω → ℝ)
    (h1 : 𝒰.Finite → ∀ ζ : ℝ, 0 < ζ → μ {h | ζ * σ₀ * W h < I h} ≤
      ENNReal.ofReal ((t : ℝ) ^ (5 * 𝒰.ncard) * Real.exp (-ζ ^ 2 / 2)))
    (h2 : ∀ ζ : ℝ, 2 ≤ ζ → μ {h | ζ * kappa0 ubar lam0 * σ₀ * Real.sqrt (Real.log t) * W h < I h} ≤
      ENNReal.ofReal ((t : ℝ) ^ ((r : ℝ) * kappa0 ubar lam0 ^ 2) * Real.exp (-ζ ^ 2 / 4))) :
    μ {h | radiusFactor 𝒰 σ₀ ubar lam0 t * W h < I h} ≤ ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
  set κ := kappa0 ubar lam0 with hκdef
  have hκ : 2 ≤ κ := kappa0_ge_two ubar lam0 hlam0
  have ht2 : 2 ≤ t := hr.trans ht
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht2
  have hLpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  -- the infinite-arm route, used whenever the width is `r log t`
  have hinf : width 𝒰 t = (r : ℝ) * Real.log t →
      μ {h | radiusFactor 𝒰 σ₀ ubar lam0 t * W h < I h} ≤ ENNReal.ofReal (1 / (t : ℝ) ^ 2) := by
    intro hw
    set ζ := 4 * κ * Real.sqrt ((r : ℝ) * Real.log t) with hζ
    have hζ2 : 2 ≤ ζ := by
      have : 1 ≤ (r : ℝ) * Real.log t := by
        have : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) htR
        have := Real.log_two_gt_d9
        nlinarith
      have : 1 ≤ Real.sqrt ((r : ℝ) * Real.log t) := by rw [Real.one_le_sqrt]; exact this
      rw [hζ]; nlinarith
    have hrf : radiusFactor 𝒰 σ₀ ubar lam0 t = ζ * κ * σ₀ * Real.sqrt (Real.log t) := by
      unfold radiusFactor alpha
      rw [hw, hζ, ← hκdef]
      ring
    rw [hrf]
    refine (h2 ζ hζ2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact infinite_num t ht2 r (by omega) κ hκ
  by_cases hfin : 𝒰.Finite
  · have hwd : width 𝒰 t = min ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) := by
      unfold width; rw [if_pos hfin]
    rcases le_or_gt ((r : ℝ) * Real.log t) (𝒰.ncard : ℝ) with hle | hlt
    · exact hinf (hwd.trans (min_eq_left hle))
    · -- finite case with `|𝒰| < r log t`
      have hn : 1 ≤ 𝒰.ncard := (Set.ncard_pos hfin).mpr h𝒰n
      have hw : width 𝒰 t = 𝒰.ncard := hwd.trans (min_eq_right hlt.le)
      set ζ := 4 * κ ^ 2 * Real.sqrt (Real.log t) * Real.sqrt (𝒰.ncard : ℝ) with hζ
      have hζpos : 0 < ζ := by
        have : (0 : ℝ) < 𝒰.ncard := by exact_mod_cast hn
        rw [hζ]; positivity
      have hrf : radiusFactor 𝒰 σ₀ ubar lam0 t = ζ * σ₀ := by
        unfold radiusFactor alpha
        rw [hw, hζ, ← hκdef]
        ring
      rw [hrf]
      refine (h1 hfin ζ hζpos).trans (ENNReal.ofReal_le_ofReal ?_)
      exact finite_num t ht2 _ hn κ hκ
  · exact hinf (by unfold width; rw [if_neg hfin])

end UEGenB6Aux

open UEGenB6Aux LinParamBandits.UEGeneral in
theorem solution {r : ℕ} (hr : 2 ≤ r) {𝒰 : Set (LinParamBandits.LowerBound.Vec r)} (h𝒰c : IsCompact 𝒰) (h𝒰n : 𝒰.Nonempty)
    {ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ} [IsMarkovKernel ν] {b : Fin r → LinParamBandits.LowerBound.Vec r} {σ₀ ubar lam0 : ℝ}
    (hA : Assumption1 𝒰 ν b σ₀ ubar lam0) {ψ : Policy r} (hψ : IsUE 𝒰 b σ₀ ubar lam0 ψ)
    (t : ℕ) (ht : r ≤ t) (z : LinParamBandits.LowerBound.Vec r) :
    (∀ u ∈ 𝒰, histMeasure ν z ψ t
        {h | radius 𝒰 σ₀ ubar lam0 h u < inner ℝ u (Zhat h - z)} ≤
      ENNReal.ofReal (1 / (t : ℝ) ^ 2)) ∧
    (∀ x : LinParamBandits.LowerBound.Vec r, histMeasure ν z ψ t
        {h | radiusFactor 𝒰 σ₀ ubar lam0 t * wnorm (Cmat (armsOf h)) (ψ.act t h - x) <
          inner ℝ (ψ.act t h - x) (Zhat h - z)} ≤
      ENNReal.ofReal (1 / (t : ℝ) ^ 2)) := by
  refine ⟨fun u _ => ?_, fun x => ?_⟩
  · exact core hr h𝒰n (histMeasure ν z ψ t) σ₀ ubar lam0 hA.σ₀_pos hA.lam0_pos t ht
      (fun h => wnorm (Cmat (armsOf h)) u) (fun h => inner ℝ u (Zhat h - z))
      (fun hfin ζ hζ => (chernoff_finite_arms hr h𝒰c h𝒰n hA hψ hfin t ht u z ζ hζ).1)
      (fun ζ hζ => (chernoff_infinite_arms hr h𝒰c h𝒰n hA hψ t ht u z ζ hζ).1)
  · exact core hr h𝒰n (histMeasure ν z ψ t) σ₀ ubar lam0 hA.σ₀_pos hA.lam0_pos t ht
      (fun h => wnorm (Cmat (armsOf h)) (ψ.act t h - x))
      (fun h => inner ℝ (ψ.act t h - x) (Zhat h - z))
      (fun hfin ζ hζ => (chernoff_finite_arms hr h𝒰c h𝒰n hA hψ hfin t ht x z ζ hζ).2)
      (fun ζ hζ => (chernoff_infinite_arms hr h𝒰c h𝒰n hA hψ t ht x z ζ hζ).2)
