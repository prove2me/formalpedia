-- Prove2me | solution 1 for Kyprianou.Ch02.levyCanonicalFiniteVariationResidualModelV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:47:17.146752+00:00
-- url     : https://prove2.me/submissions/d470c679-2924-4c26-9dd1-11cfe3c8c439

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Theorems.Thm_Kyprianou_Ch02_levyCanonicalFiniteVariationResidualExplicitModelV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Translate the explicit characteristic exponent into the Chapter 1 convention. -/
theorem solution
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) :
    ∃ (Λ : Type) (mΛ : MeasurableSpace Λ),
      letI : MeasurableSpace Λ := mΛ
      ∃ (Q : Measure Λ) (Y : ℝ≥0 → Λ → ℝ) (d : ℝ),
        IsProbabilityMeasure Q ∧ IsLevyProcess Y Q ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (Q.map (Y t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent
                ⟨-a, 0, levyMeasure, hlevyMeasure⟩ ξ)) ∧
        (∀ᵐ ω ∂Q, ∀ T : ℝ≥0,
          Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
            |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|) ∧
          Y T ω = d * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T,
              (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) := by
  obtain ⟨A, mA, M, J, d, hprob, hJ, hJchar, hres⟩ :=
    Kyprianou.Ch02.levyCanonicalFiniteVariationResidualExplicitModelV1
      a levyMeasure hlevyMeasure hfin
  refine ⟨A, mA, M, J, d, hprob, hJ, ?_, hres⟩
  intro t ξ
  rw [hJchar t ξ]
  congr 1
  dsimp [Kyprianou.Ch01.levyTripleExponent]
  push_cast
  ring
