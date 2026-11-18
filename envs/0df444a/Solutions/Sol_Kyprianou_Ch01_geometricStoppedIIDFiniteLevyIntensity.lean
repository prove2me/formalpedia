-- Prove2me | solution 1 for Kyprianou.Ch01.geometricStoppedIIDFiniteLevyIntensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:19:04.758115+00:00
-- url     : https://prove2.me/submissions/661dd785-6713-492a-9e51-12bc0b1b2266

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Theorems.Thm_Kyprianou_Ch01_logarithmicConvIntensityOffZeroFinite
import Theorems.Thm_Kyprianou_Ch01_logarithmicWeightedProbabilityMeasureSumFinite
import Theorems.Thm_Kyprianou_Ch01_finiteLevyCompensatedFourierIntegrable
import Theorems.Thm_Kyprianou_Ch01_compensatedFourierIntegralRestrictNonzero
import Theorems.Thm_Kyprianou_Ch01_logarithmicWeightedFourierIntegralSeries
import Theorems.Thm_Kyprianou_Ch01_convPowCompensatedFourierIntegral
import Theorems.Thm_Kyprianou_Ch01_geometricRandomSumCharExponent
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex LevyFoundations QueueingFundamentals.MG1
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ,
      HasLaw (increment n) jumpLaw P)
    (hGeometric : ∀ k : ℕ,
      P {ω | N ω = k} =
        ENNReal.ofReal (p * (1 - p) ^ k))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    ∃ Λ : Measure ℝ,
      Λ {0} = 0 ∧
      Λ Set.univ < ⊤ ∧
      ∀ xi : ℝ,
        Integrable (fun x : ℝ =>
          Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) Λ ∧
        Complex.exp
          (∫ x : ℝ,
            (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂Λ) =
          (p : ℂ) /
            (1 - (((1 - p : ℝ) : ℂ) * charFun jumpLaw xi)) := by
  have hq0 : 0 ≤ 1 - p := le_of_lt (sub_pos.mpr hp1)
  have hq1 : 1 - p < 1 := sub_lt_self 1 hp0
  let M : Measure ℝ := Measure.sum fun n : ℕ =>
    (ENNReal.ofReal ((1 - p) ^ (n + 1) / (n + 1 : ℝ))) •
      QueueingFundamentals.MG1.convPow jumpLaw (n + 1)
  have hprob : ∀ n : ℕ, IsProbabilityMeasure
      (QueueingFundamentals.MG1.convPow jumpLaw n) := by
    intro n
    induction n with
    | zero =>
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.dirac.isProbabilityMeasure
    | succ n hn =>
        letI := hn
        dsimp [QueueingFundamentals.MG1.convPow]
        exact Measure.probabilitymeasure_of_probabilitymeasures_conv _ _
  have hM : M Set.univ < ⊤ :=
    Kyprianou.Ch01.logarithmicWeightedProbabilityMeasureSumFinite
      (1 - p) hq0 hq1
      (fun n => QueueingFundamentals.MG1.convPow jumpLaw (n + 1))
      (fun n => hprob (n + 1))
  letI : IsFiniteMeasure M := ⟨hM⟩
  have hL : (M.restrict ({0}ᶜ)) {0} = 0 ∧
      (M.restrict ({0}ᶜ)) Set.univ < ⊤ := by
    simpa only [M] using
      Kyprianou.Ch01.logarithmicConvIntensityOffZeroFinite
        (1 - p) hq0 hq1 jumpLaw
  refine ⟨M.restrict ({0}ᶜ), hL.1, hL.2, ?_⟩
  intro xi
  letI : IsFiniteMeasure (M.restrict ({0}ᶜ)) := ⟨hL.2⟩
  refine ⟨Kyprianou.Ch01.finiteLevyCompensatedFourierIntegrable
    (M.restrict ({0}ᶜ)) xi, ?_⟩
  have hrest :=
    Kyprianou.Ch01.compensatedFourierIntegralRestrictNonzero M xi
  have hweighted :=
    Kyprianou.Ch01.logarithmicWeightedFourierIntegralSeries
      (1 - p) hq0 hq1
      (fun n => QueueingFundamentals.MG1.convPow jumpLaw (n + 1))
      (fun n => hprob (n + 1)) xi
  change (∫ x : ℝ,
    (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1) ∂M) = _ at hweighted
  have hseries :
      (∑' n : ℕ,
        (((1 - p) ^ (n + 1) / (n + 1 : ℝ) : ℝ) : ℂ) *
          (∫ x : ℝ, (Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I) - 1)
            ∂(QueueingFundamentals.MG1.convPow jumpLaw (n + 1)))) =
      (∑' n : ℕ,
        ((((1 - p : ℝ) : ℂ) ^ (n + 1)) / ((n : ℂ) + 1)) *
          ((charFun jumpLaw xi) ^ (n + 1) - 1)) := by
    apply tsum_congr
    intro n
    rw [Kyprianou.Ch01.convPowCompensatedFourierIntegral
      jumpLaw (n + 1) xi]
    push_cast
    ring
  rw [hrest, hweighted, hseries]
  exact Kyprianou.Ch01.geometricRandomSumCharExponent
    p hp0 hp1 jumpLaw xi
