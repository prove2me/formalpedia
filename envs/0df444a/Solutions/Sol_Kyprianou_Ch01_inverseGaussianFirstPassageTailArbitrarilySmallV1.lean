-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFirstPassageTailArbitrarilySmallV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:24:45.993255+00:00
-- url     : https://prove2.me/submissions/bf0c57b5-94cc-439b-8c73-f1354f74a136

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageTailMarkovBoundV1
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianLaplaceDeficitTendsZeroV1
import Theorems.Thm_Kyprianou_Ch01_vanishingLaplaceEnvelopeGivesSmallTailV1
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (hb : 0 < b)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (ε : ℝ≥0) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) :
    ∃ s : ℝ≥0, 0 < s ∧
      (P {ω | (ε : WithTop ℝ≥0) ≤
         firstUpperPassage X (s : ℝ) ω}).toReal < δ := by
  let c : ℝ := 1 - Real.exp (-(ε : ℝ))
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hc : 0 < c := by
    have hExp : Real.exp (-(ε : ℝ)) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos hεR)
    dsimp [c]
    linarith
  let E : ℝ≥0 → Set Ω :=
    fun s => {ω | (ε : WithTop ℝ≥0) ≤ firstUpperPassage X (s : ℝ) ω}
  let g : ℝ≥0 → ℝ :=
    fun s => 1 - Real.exp (-((s : ℝ) *
      (Real.sqrt (b ^ 2 + 2) - b)))
  have hg : Tendsto g (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) :=
    inverseGaussianLaplaceDeficitTendsZeroV1 b
  have hBound : ∀ s : ℝ≥0, 0 < s →
       c * (P (E s)).toReal ≤ g s := by
    intro s hs
    have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
    simpa only [c, E, g] using
      (inverseGaussianFirstPassageTailMarkovBoundV1
        P X b (s : ℝ) hb hsR hB hMeas hContinuous ε)
  exact vanishingLaplaceEnvelopeGivesSmallTailV1
    P E c hc g hg hBound δ hδ
