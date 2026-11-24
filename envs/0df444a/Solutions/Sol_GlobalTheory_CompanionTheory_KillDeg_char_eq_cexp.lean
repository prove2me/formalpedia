-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KillDeg.char_eq_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:40:49.290241+00:00
-- url     : https://prove2.me/submissions/04b2bf1a-4800-4573-a50f-24190f21cd0c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsRecurrencePolynomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillDeg
namespace GlobalTheory.CompanionTheory.KillDeg
theorem _root_.solution (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1)
    (hm : ∀ s t, χ (s + t) = χ s * χ t) : ∃ c : ℂ, ∀ t : ℝ, χ t = Complex.exp (c * t) := by
  let I : ℝ → ℂ := fun x => ∫ s in (0 : ℝ)..x, χ s
  have hI : ∀ x, HasDerivAt I (χ x) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨δ, hδ⟩ : ∃ δ, I δ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hz : I = fun _ => 0 := funext hcon
    have h1 := hI 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have hint : ∀ a b : ℝ, IntervalIntegrable χ MeasureTheory.volume a b :=
    fun a b => hc.intervalIntegrable a b
  have hid : ∀ t, χ t * I δ = I (t + δ) - I t := by
    intro t
    have h1 : ∫ s in (0 : ℝ)..δ, χ (t + s) = χ t * I δ := by
      simp only [hm, I]
      exact intervalIntegral.integral_const_mul _ _
    have h2 : ∫ s in (0 : ℝ)..δ, χ (t + s) = ∫ s in (t + 0)..(t + δ), χ s :=
      intervalIntegral.integral_comp_add_left (a := 0) (b := δ) χ t
    have h3 : I t + ∫ s in t..(t + δ), χ s = I (t + δ) :=
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)
    rw [← h1, h2, add_zero, ← h3]
    ring
  let c : ℂ := (χ δ - 1) / I δ
  have hd : ∀ t, HasDerivAt χ (c * χ t) t := by
    intro t
    have h1 : HasDerivAt (fun u => I (u + δ)) (χ (t + δ)) t := by
      simpa using (hI (t + δ)).comp_add_const t δ
    have h2 : HasDerivAt (fun u => (I (u + δ) - I u) / I δ) ((χ (t + δ) - χ t) / I δ) t :=
      (h1.sub (hI t)).div_const _
    have h3 : (fun u => (I (u + δ) - I u) / I δ) = χ := by
      funext u
      rw [← hid u]
      field_simp
    rw [h3] at h2
    have h4 : (χ (t + δ) - χ t) / I δ = c * χ t := by
      simp only [c, hm]
      field_simp
    rwa [h4] at h2
  refine ⟨c, fun t => ?_⟩
  let y : ℝ → ℂ := fun u => χ u * Complex.exp (-(c * u))
  have hy : ∀ u, HasDerivAt y 0 u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => -(c * (u : ℂ))) (-c) u := by
      have h0' : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
      have h := h0'.const_mul (-c)
      rw [mul_one] at h
      have he : (fun y : ℝ => -(c * (y : ℂ))) = fun y : ℝ => -c * (y : ℂ) := by
        funext y
        ring
      rw [he]
      exact h
    have h2 := (hd u).mul h1.cexp
    have h3 : c * χ u * Complex.exp (-(c * u)) + χ u * (Complex.exp (-(c * u)) * -c) = 0 := by
      ring
    rw [h3] at h2
    exact h2
  have hy0 : y t = y 0 :=
    is_const_of_deriv_eq_zero (fun u => (hy u).differentiableAt) (fun u => (hy u).deriv) t 0
  have hy1 : y 0 = 1 := by simp [y, h0]
  have h5 : χ t * Complex.exp (-(c * t)) = 1 := by
    have : y t = 1 := hy0.trans hy1
    exact this
  rw [Complex.exp_neg] at h5
  have hne := Complex.exp_ne_zero (c * t)
  field_simp at h5
  exact h5
end GlobalTheory.CompanionTheory.KillDeg
