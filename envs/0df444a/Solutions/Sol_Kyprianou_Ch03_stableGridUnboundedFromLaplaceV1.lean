-- Prove2me | solution 1 for Kyprianou.Ch03.stableGridUnboundedFromLaplaceV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:59:17.616151+00:00
-- url     : https://prove2.me/submissions/4e0b48bb-0121-4a55-8978-0f162018cc63

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_stableGridLaplaceThresholdNullV1
import Theorems.Thm_Kyprianou_Ch03_stableGridUnboundedMeasurableV1
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, AEMeasurable (Y n) P) (hnon : ∀ n, 0 ≤ᵐ[P] Y n)
    (hlim : Tendsto (fun n => ∫ w, Real.exp (-Y n w) ∂P) atTop (𝓝 0)) :
    ∀ᵐ w ∂P, ∀ M : ℝ, ∃ n : ℕ, M < Y n w := by
  let Z : ℕ → Ω → ℝ := fun n => (hY n).mk (Y n)
  have hz (n : ℕ) : Measurable (Z n) := (hY n).measurable_mk
  have heq (n : ℕ) : Y n =ᵐ[P] Z n := (hY n).ae_eq_mk
  have hzn (n : ℕ) : 0 ≤ᵐ[P] Z n := by
    filter_upwards [hnon n, heq n] with w hw he
    simpa only [← he] using hw
  have hlimZ : Tendsto (fun n => ∫ w, Real.exp (-Z n w) ∂P) atTop (𝓝 0) := by
    convert hlim using 1
    funext n
    apply integral_congr_ae
    filter_upwards [heq n] with w hw
    rw [hw]
  have hnull (m : ℕ) := Kyprianou.Ch03.stableGridLaplaceThresholdNullV1 P Z hz hzn hlimZ (m : ℝ)
  filter_upwards [Kyprianou.Ch03.stableGridUnboundedMeasurableV1 P Z hnull,
    ae_all_iff.mpr heq] with w hw he
  intro M
  obtain ⟨n, hn⟩ := hw M
  exact ⟨n, by rwa [he n]⟩
