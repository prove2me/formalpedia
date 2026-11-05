-- Prove2me | solution 1 for GraphonGames.Existence.lemma_3_7_best_response_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T17:49:09.13921+00:00
-- url     : https://prove2.me/submissions/bc01e5f9-c282-4fa2-8e00-5f36b047e7d1

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

open GraphonGames.Existence

theorem solution (J : ℝ → ℝ → ℝ) (ℓc ℓJ : ℝ) (h4 : Asm4 J ℓc ℓJ)
    (z1 z2 : I → ℝ) (hz1 : MemLp z1 2 volume) (hz2 : MemLp z2 2 volume) :
    eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume ≤
      ENNReal.ofReal (ℓJ / ℓc) * eLpNorm (z1 - z2) 2 volume := by
  obtain ⟨hℓc, hℓJ, hC1, hconv, hderiv⟩ := h4
  -- derivative of `J · t`
  have hdiff : ∀ t, Differentiable ℝ (fun a => J a t) := fun t =>
    (hC1 t).differentiable (by norm_num)
  have hHD : ∀ t x, HasDerivAt (fun a => J a t) (deriv (fun a => J a t) x) x := fun t x =>
    (hdiff t x).hasDerivAt
  -- `J · t - ℓc/2 a²` is convex
  have hcvx : ∀ t, ConvexOn ℝ Set.univ (fun a => J a t - ℓc / 2 * a ^ 2) := by
    intro t
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    have ha1 : a ≤ 1 := by linarith
    have key := hconv x y t a ha ha1
    simp only [smul_eq_mul]
    have habs : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
    rw [habs] at key
    have hid : (a * x + (1 - a) * y) ^ 2 = a * x ^ 2 + (1 - a) * y ^ 2 - a * (1 - a) * (x - y) ^ 2 := by
      ring
    rw [hid]
    nlinarith [key]
  -- tangent-line inequality with quadratic gain
  have htan : ∀ t x y, J x t + deriv (fun a => J a t) x * (y - x) + ℓc / 2 * (y - x) ^ 2 ≤ J y t := by
    intro t x y
    have hh : HasDerivAt (fun a => J a t - ℓc / 2 * a ^ 2)
        (deriv (fun a => J a t) x - ℓc / 2 * (2 * x)) x := by
      refine HasDerivAt.congr_deriv ((hHD t x).sub ((hasDerivAt_pow 2 x).const_mul (ℓc / 2))) ?_
      simp
    rcases lt_trichotomy x y with hxy | rfl | hxy
    · have := (hcvx t).le_slope_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hh
      rw [slope_def_field, le_div_iff₀ (by linarith)] at this
      nlinarith [this]
    · simp
    · have := (hcvx t).slope_le_of_hasDerivAt (Set.mem_univ _) (Set.mem_univ _) hxy hh
      rw [slope_def_field, div_le_iff₀ (by linarith)] at this
      nlinarith [this]
  -- strong monotonicity of the derivative
  have hmono : ∀ t x y, ℓc * (y - x) ^ 2 ≤
      (deriv (fun a => J a t) y - deriv (fun a => J a t) x) * (y - x) := by
    intro t x y
    have h1 := htan t x y
    have h2 := htan t y x
    nlinarith [h1, h2]
  -- existence of a minimizer
  have hex : ∀ t, ∃ m, ∀ β, J m t ≤ J β t := by
    intro t
    set g := deriv (fun a => J a t)
    have hgc : Continuous g := (hC1 t).continuous_deriv (by norm_num)
    set M := |g 0| / ℓc + 1
    have hM : 0 < M := by positivity
    have hgM : 0 ≤ g M := by
      have := hmono t 0 M
      have h' : ℓc * M ≤ g M - g 0 := by
        by_contra hc
        push Not at hc
        nlinarith
      have : |g 0| / ℓc * ℓc = |g 0| := div_mul_cancel₀ _ hℓc.ne'
      nlinarith [neg_abs_le (g 0)]
    have hgM' : g (-M) ≤ 0 := by
      have := hmono t (-M) 0
      have h' : ℓc * M ≤ g 0 - g (-M) := by
        by_contra hc
        push Not at hc
        nlinarith
      have : |g 0| / ℓc * ℓc = |g 0| := div_mul_cancel₀ _ hℓc.ne'
      nlinarith [le_abs_self (g 0)]
    obtain ⟨r, -, hr⟩ := intermediate_value_Icc (by linarith : -M ≤ M) hgc.continuousOn
      ⟨hgM', hgM⟩
    refine ⟨r, fun β => ?_⟩
    have := htan t r β
    have hr' : deriv (fun a => J a t) r = 0 := hr
    rw [hr'] at this
    nlinarith [sq_nonneg (β - r)]
  set A : ℝ → ℝ := fun t => Classical.epsilon (fun a => ∀ β, J a t ≤ J β t) with hA
  have hAmin : ∀ t β, J (A t) t ≤ J β t := fun t => Classical.epsilon_spec (hex t)
  have hAder : ∀ t, deriv (fun a => J a t) (A t) = 0 := by
    intro t
    have : IsLocalMin (fun a => J a t) (A t) :=
      Filter.Eventually.of_forall fun β => hAmin t β
    exact this.deriv_eq_zero
  -- Lipschitz bound for the minimizer map
  have hAlip : ∀ t1 t2, |A t1 - A t2| ≤ ℓJ / ℓc * |t1 - t2| := by
    intro t1 t2
    have hm := hmono t1 (A t2) (A t1)
    rw [hAder t1] at hm
    have hd := hderiv (A t2) t1 t2
    rw [hAder t2] at hd
    have hd' : |deriv (fun a => J a t1) (A t2)| ≤ ℓJ * |t1 - t2| := by
      rw [abs_sub_comm t1 t2]; simpa using hd
    set d := A t1 - A t2
    set e := deriv (fun a => J a t1) (A t2)
    have h1 : ℓc * |d| ^ 2 ≤ ℓJ * |t1 - t2| * |d| := by
      rw [sq_abs]
      have : -e * d ≤ |e| * |d| := by
        have := neg_le_abs (e * d); rw [abs_mul] at this; linarith
      nlinarith [abs_nonneg d, mul_le_mul_of_nonneg_right hd' (abs_nonneg d)]
    rcases (abs_nonneg d).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · rw [div_mul_eq_mul_div, le_div_iff₀ hℓc]
      nlinarith
  -- conclude
  have hpt : ∀ x, ‖(bestResponse J z1 - bestResponse J z2) x‖ ≤ ‖((ℓJ / ℓc) • (z1 - z2)) x‖ := by
    intro x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Real.norm_eq_abs, bestResponse]
    rw [abs_mul, abs_of_nonneg (div_nonneg hℓJ hℓc.le)]
    exact hAlip (z1 x) (z2 x)
  calc eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume
      ≤ eLpNorm ((ℓJ / ℓc) • (z1 - z2)) 2 volume := eLpNorm_mono hpt
    _ = ENNReal.ofReal (ℓJ / ℓc) * eLpNorm (z1 - z2) 2 volume := by
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg (div_nonneg hℓJ hℓc.le)]
