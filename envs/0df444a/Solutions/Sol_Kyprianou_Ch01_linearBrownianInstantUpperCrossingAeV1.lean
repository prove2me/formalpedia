-- Prove2me | solution 1 for Kyprianou.Ch01.linearBrownianInstantUpperCrossingAeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:24:58.916321+00:00
-- url     : https://prove2.me/submissions/3e58528c-d2b7-497f-9a3a-257db4989c9f

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageTailArbitrarilySmallV1
import Theorems.Thm_Kyprianou_Ch01_smallPassageAeOfArbitrarilySmallTailV1
import Theorems.Thm_Kyprianou_Ch01_aeInstantCrossingOfCountableSmallPassagesV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω)) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, 0 < t ∧ t < ε ∧ 0 < X t ω := by
  let δ : ℕ → ℝ≥0 :=
    fun n => (1 : ℝ≥0) / ((n : ℝ≥0) + 1)
  have hδlim : Tendsto δ atTop (𝓝 (0 : ℝ≥0)) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  have hδ : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, δ n < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_order.1 hδlim).2 ε hε).exists
    exact ⟨n, hn⟩
  have hSmall : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∃ s : ℝ≥0, 0 < s ∧
        firstUpperPassage X (s : ℝ) ω <
          (δ n : WithTop ℝ≥0) := by
    intro n
    have hδPos : 0 < δ n := by
      dsimp [δ]
      positivity
    apply smallPassageAeOfArbitrarilySmallTailV1 P X (δ n)
    intro η hη
    exact inverseGaussianFirstPassageTailArbitrarilySmallV1
      P X b hb hB hMeas hContinuous (δ n) hδPos η hη
  exact aeInstantCrossingOfCountableSmallPassagesV1
    P X δ hδ hSmall

