-- Prove2me | solution 1 for MasulloRH.rigidity_of_common_smoothed_radial_tail
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T03:44:26.566954+00:00
-- url     : https://prove2.me/submissions/6a51bfda-b403-40c5-bae4-f1915bb1ca08

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
open Filter MeasureTheory
open scoped Topology
theorem solution (μ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μ n)]
    (F : ℝ → ℂ) (hF : ∀ n, Integrable F (μ n)) (A : ℝ) (C : ℂ)
    (hes : ∀ a : ℝ, ∀ᶠ n in atTop, ∀ᵐ x ∂μ n, a ≤ x)
    (hlim : ∀ a ≥ A, Tendsto (fun n => ∫ x, F x - F a ∂μ n) atTop (𝓝 C)) :
    C = 0 ∧ ∀ a ≥ A, F a = F A := by
  have hi (a : ℝ) (n : ℕ) : (∫ x, F x - F a ∂μ n) = (∫ x, F x ∂μ n) - F a := by
    rw [integral_sub (hF n) (integrable_const _)]
    simp
  have hl (a : ℝ) (ha : A ≤ a) :
      Tendsto (fun n => ∫ x, F x ∂μ n) atTop (𝓝 (C + F a)) := by
    have H := (hlim a ha).add_const (F a)
    simpa only [hi, sub_add_cancel] using H
  have hc (a : ℝ) (ha : A ≤ a) : F a = F A := by
    exact add_left_cancel (tendsto_nhds_unique (hl a ha) (hl A le_rfl))
  refine ⟨?_, hc⟩
  have he : (fun n => ∫ x, F x - F A ∂μ n) =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [hes A] with n hn
    have hz : (fun x => F x - F A) =ᵐ[μ n] fun _ => (0 : ℂ) := by
      filter_upwards [hn] with x hx
      exact sub_eq_zero.mpr (hc x hx)
    simpa using integral_congr_ae hz
  exact tendsto_nhds_unique (hlim A le_rfl) (tendsto_const_nhds.congr' he.symm)
