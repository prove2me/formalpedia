-- Prove2me | solution 1 for Kyprianou.Ch04.bvCanonicalPoissonExactDriftV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:42:07.399844+00:00
-- url     : https://prove2.me/submissions/f5465261-5e81-428a-a16a-98ceb8e3a2e0

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
import Theorems.Thm_Kyprianou_Ch02_levyPoissonPathFiniteVariationResidualV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Canonical Poisson model, keeping the characteristic exponent explicit. -/
theorem solution
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (hfin : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure) :
    ∃ (Λ : Type) (mΛ : MeasurableSpace Λ),
      letI : MeasurableSpace Λ := mΛ
      ∃ (Q : Measure Λ) (Y : ℝ≥0 → Λ → ℝ),
        IsProbabilityMeasure Q ∧ IsLevyProcess Y Q ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (Q.map (Y t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              (Complex.I * (((-a) * ξ : ℝ) : ℂ) +
                ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) ∧
        (∀ᵐ ω ∂Q, ∀ T : ℝ≥0,
          Summable (fun s : Set.Ioc (0 : ℝ≥0) T =>
            |Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0)|) ∧
          Y T ω = (-a - ∫ x in Set.Ioo (-1 : ℝ) 1, x ∂levyMeasure) * (T : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) T,
              (Y (s : ℝ≥0) ω - leftLim (fun u : ℝ≥0 => Y u ω) (s : ℝ≥0))) := by
  haveI := hlevyMeasure.sigmaFinite
  obtain ⟨A, mA, M, K, Z, hprob, hd⟩ :=
    ProbabilityTheory.exists_isPoissonPointFamily ((volume : Measure ℝ).prod levyMeasure)
  letI : MeasurableSpace A := mA
  letI : IsProbabilityMeasure M := hprob
  let J := ProbabilityTheory.levyJumpPath hd hlevyMeasure (-a)
  refine ⟨A, mA, M, J,
    hprob, ProbabilityTheory.isLevyProcess_levyJumpPath hd hlevyMeasure (-a), ?_, ?_⟩
  · intro t ξ
    have hChar := ProbabilityTheory.charFun_map_levyJumpPath hd hlevyMeasure (-a) t ξ
    rw [ProbabilityTheory.LevyKhintchineTriple.exponent_def] at hChar
    simp only [NNReal.coe_zero, Complex.ofReal_zero, zero_mul, zero_div, sub_zero] at hChar
    convert hChar using 1 <;> congr 1 <;> push_cast <;> ring
  · exact Kyprianou.Ch02.levyPoissonPathFiniteVariationResidualV1
      M levyMeasure K Z hd hlevyMeasure (-a) hfin
