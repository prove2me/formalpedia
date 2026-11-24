-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_density_lintegral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:39:32.131827+00:00
-- url     : https://prove2.me/submissions/8abe7bd2-4e5c-484f-a4d2-281a5f538ac9

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
open Kyprianou.Ch08.StageB
/-- Conditional density-side sequential limit for the zero-discount occupation identity. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a → ∀ y : ℝ, Tendsto
        (fun n : ℕ => ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y)) atTop
        (𝓝 (ENNReal.ofReal (killedIntervalDensity (W 0) a x y)))) →
    (∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
      (W : ℝ → ℝ → ℝ),
      IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
      HasSourceScaleFamily ψ W →
      ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a → ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y) ≤
        ENNReal.ofReal (W 1 x * W 1 a / W 0 a + W 1 x)) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ (A : Set ℝ), MeasurableSet A →
        Tendsto
          (fun n : ℕ =>
            ((volume.restrict (Set.Icc 0 a)).withDensity
              (fun y : ℝ => ENNReal.ofReal
                (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y))) A)
          atTop
          (𝓝 (((volume.restrict (Set.Icc 0 a)).withDensity
            (fun y : ℝ => ENNReal.ofReal
              (killedIntervalDensity (W 0) a x y))) A)) := by
  intro Ω mΩ P hP D ψ W hψ hW hpoint_fn hbound_fn a x ha hx hxa A hA
  let qseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hpoint := hpoint_fn Ω P D ψ W hψ hW a x ha hx hxa
  have hbound := hbound_fn Ω P D ψ W hψ hW a x ha hx hxa
  let C : ℝ := W 1 x * W 1 a / W 0 a + W 1 x
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 a)
  let F : ℕ → ℝ → ENNReal := fun n y =>
    A.indicator (fun z : ℝ =>
      ENNReal.ofReal (killedIntervalDensity (W (qseq n)) a x z)) y
  let f : ℝ → ENNReal := fun y =>
    A.indicator (fun z : ℝ =>
      ENNReal.ofReal (killedIntervalDensity (W 0) a x z)) y
  have hW_meas : ∀ n : ℕ, Measurable (W (qseq n)) := by
    intro n
    rcases hW (qseq n) (by dsimp [qseq]; positivity) with
      ⟨_, hneg, hnon, _, hmonoOn, _⟩
    exact Monotone.measurable (by
      intro u v huv
      by_cases hu : u < 0
      · simpa [hneg u hu] using hnon v
      · exact hmonoOn (le_of_not_gt hu) (le_trans (le_of_not_gt hu) huv) huv)
  have hF_meas : ∀ n : ℕ, Measurable (F n) := by
    intro n
    have hWn := hW_meas n
    dsimp [F, killedIntervalDensity]
    measurability
  have hbound_ae : ∀ n : ℕ,
      F n ≤ᵐ[μ] (fun _ : ℝ => ENNReal.ofReal C) := by
    intro n
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with y hyI
    by_cases hyA : y ∈ A
    · simpa [F, hyA, qseq, C] using hbound n y hyI
    · simp [F, hyA]
  have hbound_int : (∫⁻ y : ℝ, ENNReal.ofReal C ∂μ) ≠ ⊤ := by
    simp [μ, ha.le]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hpoint_ae :
      ∀ᵐ y : ℝ ∂μ, Tendsto (fun n : ℕ => F n y) atTop (𝓝 (f y)) := by
    exact Filter.Eventually.of_forall (fun y : ℝ => by
      by_cases hy : y ∈ A
      · simpa [F, f, hy, qseq] using hpoint y
      · simp [F, f, hy])
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := μ) (F := F) (f := f)
    (fun _ : ℝ => ENNReal.ofReal C)
    hF_meas hbound_ae hbound_int hpoint_ae
  have hsetlim :
      Tendsto (fun n : ℕ =>
        ∫⁻ y : ℝ in A,
          ENNReal.ofReal (killedIntervalDensity (W (qseq n)) a x y) ∂μ)
        atTop
        (𝓝 (∫⁻ y : ℝ in A,
          ENNReal.ofReal (killedIntervalDensity (W 0) a x y) ∂μ)) := by
    simpa [F, f, MeasureTheory.lintegral_indicator hA] using hlim
  simpa [μ, qseq, MeasureTheory.withDensity_apply _ hA] using hsetlim

