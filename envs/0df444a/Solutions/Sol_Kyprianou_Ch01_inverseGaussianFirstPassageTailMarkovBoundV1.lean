-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianFirstPassageTailMarkovBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:22:40.006977+00:00
-- url     : https://prove2.me/submissions/78b8c5c1-36d5-4116-b79d-c5fecc7e2278

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_probabilityDeficitMarkovBoundV1
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceDeficitEventSubsetV1
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassageLaplaceIntegrableOfContinuousPublic
import Theorems.Thm_Kyprianou_Ch01_inverseGaussianFirstPassageLaplaceRightContinuous
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (b s : ℝ) (hb : 0 < b) (hs : 0 < s)
    (hB : IsLinearBrownian P X 1 b)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (ε : ℝ≥0) :
    (1 - Real.exp (-(ε : ℝ))) *
      (P {ω | (ε : WithTop ℝ≥0) ≤ firstUpperPassage X s ω}).toReal ≤
    1 - Real.exp (-(s * (Real.sqrt (b ^ 2 + 2) - b))) := by
  let f : Ω → ℝ := passageLaplace (firstUpperPassage X s) 1
  have hfInt : Integrable f P :=
    firstUpperPassageLaplaceIntegrableOfContinuousPublic
      P X hMeas hContinuous s 1 (by norm_num)
  have hfLe : ∀ᵐ ω ∂P, f ω ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    cases hT : firstUpperPassage X s ω with
    | top => simp [f, passageLaplace, hT]
    | coe t =>
        have ht : Real.exp (-(t : ℝ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (NNReal.coe_nonneg t))
        simpa [f, passageLaplace, hT] using ht
  have hMarkov :=
    probabilityDeficitMarkovBoundV1 P f hfInt hfLe
      (1 - Real.exp (-(ε : ℝ)))
  have hSub :
      {ω | (ε : WithTop ℝ≥0) ≤ firstUpperPassage X s ω} ⊆
        {ω | 1 - Real.exp (-(ε : ℝ)) ≤ 1 - f ω} := by
    simpa only [f] using
      (passageLaplaceDeficitEventSubsetV1 X s ε)
  have hFin :
      P {ω | 1 - Real.exp (-(ε : ℝ)) ≤ 1 - f ω} ≠ ⊤ := by
    have hOne :
        P {ω | 1 - Real.exp (-(ε : ℝ)) ≤ 1 - f ω} ≤ 1 := by
      calc
        _ ≤ P Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ne_of_lt (lt_of_le_of_lt hOne (by simp))
  have hR : (P {ω | (ε : WithTop ℝ≥0) ≤
        firstUpperPassage X s ω}).toReal ≤
      (P {ω | 1 - Real.exp (-(ε : ℝ)) ≤ 1 - f ω}).toReal :=
    ENNReal.toReal_mono hFin (measure_mono hSub)
  have hC : 0 ≤ 1 - Real.exp (-(ε : ℝ)) := by
    have he : Real.exp (-(ε : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (NNReal.coe_nonneg ε))
    linarith
  have hMean : (∫ ω, f ω ∂P) =
      Real.exp (-(s * (Real.sqrt (b ^ 2 + 2) - b))) := by
    simpa [f] using
      (inverseGaussianFirstPassageLaplaceRightContinuous
        P X b s hb hs hB hMeas hContinuous).2 1 (by norm_num)
  calc
    _ ≤ (1 - Real.exp (-(ε : ℝ))) *
        (P {ω | 1 - Real.exp (-(ε : ℝ)) ≤ 1 - f ω}).toReal :=
      mul_le_mul_of_nonneg_left hR hC
    _ ≤ 1 - ∫ ω, f ω ∂P := hMarkov
    _ = _ := by rw [hMean]
