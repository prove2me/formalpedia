-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.qzero_killed_density_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T02:13:13.994887+00:00
-- url     : https://prove2.me/submissions/4ca2416a-4923-460c-9661-942944d4680a

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal Topology
open Kyprianou.Ch08.StageB
/-- Conditional uniform dominant for the killed interval density. -/
theorem solution :
    ∀ (Ω : Type) [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (W : ℝ → ℝ → ℝ),
    IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ →
    HasSourceScaleFamily ψ W →
    (∀ a : ℝ, 0 < a → 0 < W 0 a) →
    (∀ {r s z : ℝ}, 0 ≤ r → 0 ≤ s → r ≤ s → 0 ≤ z → W r z ≤ W s z) →
    (∀ z : ℝ, z < 0 → ∀ q : ℝ, 0 ≤ q → W q z = 0) →
    (∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        W (((n : ℝ) + 1)⁻¹) x * W (((n : ℝ) + 1)⁻¹) (a - y) /
            W (((n : ℝ) + 1)⁻¹) a
          ≤ W 1 x * W 1 a / W 0 a) →
    ∀ (a x : ℝ), 0 < a → 0 ≤ x → x ≤ a →
      ∀ n : ℕ, ∀ y ∈ Set.Icc (0 : ℝ) a,
        ENNReal.ofReal
          (killedIntervalDensity (W (((n : ℝ) + 1)⁻¹)) a x y) ≤
        ENNReal.ofReal (W 1 x * W 1 a / W 0 a + W 1 x) := by
  intro Ω mΩ P hP D ψ W hψ hW hden hmono0 hnegzero hratio a x ha hx hxa
  let qseq : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hqseq_pos : ∀ n, 0 < qseq n := by
    intro n
    dsimp [qseq]
    positivity
  have hqseq_le_one : ∀ n, qseq n ≤ 1 := by
    intro n
    dsimp [qseq]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    exact inv_le_one_of_one_le₀ h1
  intro n y hy
  have hratio' : W (qseq n) x * W (qseq n) (a - y) / W (qseq n) a ≤
      W 1 x * W 1 a / W 0 a := by
    simpa [qseq] using hratio a x ha hx hxa n y hy
  have hneg_shift : -W (qseq n) (x - y) ≤ W 1 x := by
    by_cases hxy : 0 ≤ x - y
    · have hWq_nonneg : 0 ≤ W (qseq n) (x - y) :=
        (hW (qseq n) (le_of_lt (hqseq_pos n))).2.2.1 (x - y)
      have hW1_nonneg : 0 ≤ W 1 x := (hW 1 zero_le_one).2.2.1 x
      linarith
    · have hneg : x - y < 0 := lt_of_not_ge hxy
      rw [hnegzero (x - y) hneg (qseq n) (le_of_lt (hqseq_pos n))]
      have hW1_nonneg : 0 ≤ W 1 x := (hW 1 zero_le_one).2.2.1 x
      linarith
  have hbound : W (qseq n) x * W (qseq n) (a - y) / W (qseq n) a - W (qseq n) (x - y)
      ≤ W 1 x * W 1 a / W 0 a + W 1 x := by
    linarith [hratio', hneg_shift]
  apply ENNReal.ofReal_le_ofReal
  simpa [killedIntervalDensity, qseq] using hbound
