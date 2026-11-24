-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_killed_density_pointwise_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:12:59.227599+00:00
-- url     : https://prove2.me/submissions/740c8ce1-7a13-41f9-953f-495c103940f8

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
open Kyprianou.Ch08.StageB
/-- Conditional pointwise zero-discount convergence of the killed interval density. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ a : ℝ, 0 < a → 0 < W 0 a) →
    (∀ z : ℝ, 0 ≤ z →
      Tendsto (fun n : ℕ => W (((n : ℝ) + 1)⁻¹) z) atTop (𝓝 (W 0 z))) →
    (∀ z : ℝ, z < 0 → ∀ q : ℝ, 0 ≤ q → W q z = 0) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ y : ℝ, Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y)) atTop
        (𝓝 (ENNReal.ofReal (killedIntervalDensity (W 0) a x y))) := by
  intro Ω mΩ P hP D ψ W hψ hW hden hcont hnegzero a x ha hx hxa
  let qseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hqseq_pos : ∀ n, 0 < qseq n := by
    intro n
    dsimp [qseq]
    positivity
  have hscale_tendsto : ∀ z : ℝ, 0 ≤ z →
      Tendsto (fun n : ℕ => W (qseq n) z) atTop (𝓝 (W 0 z)) := by
    intro z hz
    simpa [qseq] using hcont z hz
  have hden_pos : 0 < W 0 a := hden a ha
  have hzero_neg : ∀ {z : ℝ}, z < 0 → ∀ n, W (qseq n) z = 0 := by
    intro z hz n
    exact hnegzero z hz (qseq n) (le_of_lt (hqseq_pos n))
  have hdens_tendsto : ∀ y : ℝ,
      Tendsto (fun n : ℕ => ENNReal.ofReal (killedIntervalDensity (W (qseq n)) a x y))
        atTop (𝓝 (ENNReal.ofReal (killedIntervalDensity (W 0) a x y))) := by
    intro y
    have hxlim := hscale_tendsto x hx
    have halim : Tendsto (fun n : ℕ => W (qseq n) (a - y)) atTop
        (𝓝 (W 0 (a - y))) := by
      by_cases h : 0 ≤ a - y
      · exact hscale_tendsto (a - y) h
      · have hneg : a - y < 0 := lt_of_not_ge h
        have hW0 : W 0 (a - y) = 0 := hnegzero (a - y) hneg 0 le_rfl
        have hWn : ∀ n, W (qseq n) (a - y) = 0 := fun n => hzero_neg hneg n
        simp only [hWn, hW0]
        exact tendsto_const_nhds
    have hdenlim := hscale_tendsto a (le_of_lt ha)
    have hdiff : Tendsto (fun n : ℕ => W (qseq n) (x - y)) atTop
        (𝓝 (W 0 (x - y))) := by
      by_cases h : 0 ≤ x - y
      · exact hscale_tendsto (x - y) h
      · have hneg : x - y < 0 := lt_of_not_ge h
        have hW0 : W 0 (x - y) = 0 := hnegzero (x - y) hneg 0 le_rfl
        have hWn : ∀ n, W (qseq n) (x - y) = 0 := fun n => hzero_neg hneg n
        simp only [hWn, hW0]
        exact tendsto_const_nhds
    have hratio : Tendsto (fun n : ℕ =>
        W (qseq n) x * W (qseq n) (a - y) / W (qseq n) a) atTop
        (𝓝 (W 0 x * W 0 (a - y) / W 0 a)) := by
      exact (hxlim.mul halim).div hdenlim (ne_of_gt hden_pos)
    have hreal : Tendsto (fun n : ℕ => killedIntervalDensity (W (qseq n)) a x y)
        atTop (𝓝 (killedIntervalDensity (W 0) a x y)) := by
      simpa [killedIntervalDensity] using hratio.sub hdiff
    exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal).congr fun _ => rfl
  intro y
  simpa [qseq] using hdens_tendsto y

