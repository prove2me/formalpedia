-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CharDeriv.hasDerivAt_of_continuous_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:22:48.887197+00:00
-- url     : https://prove2.me/submissions/c83780fe-34ff-4f86-8915-df52a136f013

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtOfContinuousHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CharDeriv
namespace GlobalTheory.CompanionTheory.CharDeriv
theorem _root_.solution :
    ∀ (χ : ℝ → ℂ), Continuous χ → χ 0 = 1 → (∀ s t, χ (s + t) = χ s * χ t) →
      ∃ c : ℂ, ∀ t, HasDerivAt χ (c * χ t) t := by
  intro χ hc h0 hadd
  have hP : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) (χ x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  obtain ⟨δ, hI⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, χ s) ≠ 0 := by
    by_contra h
    push_neg at h
    have hz : (fun y : ℝ => ∫ s in (0 : ℝ)..y, χ s) = fun _ => (0 : ℂ) := funext h
    have h1 := hP 0
    rw [hz] at h1
    have h2 := h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
    rw [h0] at h2
    exact one_ne_zero h2
  have key : ∀ t : ℝ, χ t = ((∫ s in (0 : ℝ)..(t + δ), χ s) - ∫ s in (0 : ℝ)..t, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s) := by
    intro t
    rw [eq_div_iff hI, ← intervalIntegral.integral_const_mul]
    have h1 : (∫ s in (0 : ℝ)..δ, χ t * χ s) = ∫ u in t..(t + δ), χ u := by
      have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := δ) (fun u => χ u) t
      rw [add_zero] at h2
      rw [← h2]
      exact intervalIntegral.integral_congr fun s _ => (hadd t s).symm
    rw [h1]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)).symm
  refine ⟨(χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s), fun t => ?_⟩
  have hD : HasDerivAt (fun y : ℝ => ((∫ s in (0 : ℝ)..(y + δ), χ s) - ∫ s in (0 : ℝ)..y, χ s) /
      (∫ s in (0 : ℝ)..δ, χ s)) ((χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s)) t := by
    have h3 : HasDerivAt (fun y : ℝ => ∫ s in (0 : ℝ)..(y + δ), χ s) (χ (t + δ)) t := by
      simpa using (hP (t + δ)).comp_add_const t δ
    exact (h3.sub (hP t)).div_const _
  have hval : (χ δ - 1) / (∫ s in (0 : ℝ)..δ, χ s) * χ t =
      (χ (t + δ) - χ t) / (∫ s in (0 : ℝ)..δ, χ s) := by
    rw [hadd t δ]
    ring
  rw [hval]
  exact hD.congr_of_eventuallyEq (Filter.Eventually.of_forall key)
end GlobalTheory.CompanionTheory.CharDeriv
