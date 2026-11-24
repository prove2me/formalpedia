-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_killed_density_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:13:53.130588+00:00
-- url     : https://prove2.me/submissions/e0626665-8191-4d7f-9fb6-a6d5ba58d9b4

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
open Kyprianou.Ch08.StageB
/-- Conditional uniform ratio bound for the killed interval density. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ a : ℝ, 0 < a → 0 < W 0 a) →
    (∀ {r s z : ℝ}, 0 ≤ r → 0 ≤ s → r ≤ s → 0 ≤ z → W r z ≤ W s z) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        W (((n : ℝ) + 1)⁻¹) x * W (((n : ℝ) + 1)⁻¹) (a - y) /
            W (((n : ℝ) + 1)⁻¹) a
          ≤ W 1 x * W 1 a / W 0 a := by
  intro Ω mΩ P hP D ψ W hψ hW hden hmono0 a x ha hx hxa
  let qseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hqseq_pos : ∀ n, 0 < qseq n := by
    intro n
    dsimp [qseq]
    positivity
  have hqseq_le_one : ∀ n, qseq n ≤ 1 := by
    intro n
    dsimp [qseq]
    exact inv_le_one_of_one_le₀ (by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  have hden_pos : 0 < W 0 a := hden a ha
  intro n y hy
  have hy0 : 0 ≤ y := hy.1
  have hya : y ≤ a := hy.2
  have hq0 : 0 ≤ qseq n := le_of_lt (hqseq_pos n)
  have hqScale := hW (qseq n) hq0
  have h1Scale := hW 1 zero_le_one
  have hq_nonneg : ∀ z : ℝ, 0 ≤ W (qseq n) z := hqScale.2.2.1
  have h1_nonneg : ∀ z : ℝ, 0 ≤ W 1 z := h1Scale.2.2.1
  have h1_monotone : MonotoneOn (W 1) (Set.Ici (0 : ℝ)) := h1Scale.2.2.2.2.1
  have hxle : W (qseq n) x ≤ W 1 x := hmono0 hq0 zero_le_one (hqseq_le_one n) hx
  have hale : W (qseq n) (a - y) ≤ W 1 a := by
    have hay0 : 0 ≤ a - y := sub_nonneg.mpr hya
    have hle1 : W (qseq n) (a - y) ≤ W 1 (a - y) :=
      hmono0 hq0 zero_le_one (hqseq_le_one n) hay0
    have hay_a : a - y ≤ a := by
      linarith [hy0]
    exact le_trans hle1 (h1_monotone hay0 (le_of_lt ha) hay_a)
  have hden_lower : W 0 a ≤ W (qseq n) a :=
    hmono0 le_rfl hq0 (le_of_lt (hqseq_pos n)) (le_of_lt ha)
  have hqden_pos : 0 < W (qseq n) a := lt_of_lt_of_le hden_pos hden_lower
  have hWqx_nonneg : 0 ≤ W (qseq n) x := hq_nonneg x
  have hWqay_nonneg : 0 ≤ W (qseq n) (a - y) := hq_nonneg (a - y)
  have hW1x_nonneg : 0 ≤ W 1 x := h1_nonneg x
  have hW1a_nonneg : 0 ≤ W 1 a := h1_nonneg a
  have hnum : W (qseq n) x * W (qseq n) (a - y) ≤ W 1 x * W 1 a :=
    mul_le_mul hxle hale hWqay_nonneg hW1x_nonneg
  have hdiv : W (qseq n) x * W (qseq n) (a - y) / W (qseq n) a ≤
      W 1 x * W 1 a / W 0 a := by
    gcongr <;> positivity
  simpa [qseq] using hdiv
