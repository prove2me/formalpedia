-- Prove2me | solution 1 for Kyprianou.Ch02.levyCanonicalPureJumpExplicitModelV1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T04:51:52.394953+00:00
-- url     : https://prove2.me/submissions/4abaf55f-db8b-4aca-ac44-b229a15e5a78

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_ProbabilityTheory_isLevyProcess_levyJumpPath
import Theorems.Thm_ProbabilityTheory_measurable_levyJumpPath
import Theorems.Thm_ProbabilityTheory_charFun_map_levyJumpPath
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
import Theorems.Thm_Kyprianou_Ch02_levyPoissonPathSmallJumpMassMeanBoundV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    : ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ t, Measurable (X t)) ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (P.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              (Complex.I * (((-a) * ξ : ℝ) : ℂ) +
                ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure))) ∧
        (∀ n : ℕ,
          (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal
          (if |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)| ≤ (1 : ℝ)
           then |X (s : ℝ≥0) ω -
                Function.leftLim (fun u : ℝ≥0 => X u ω) (s : ℝ≥0)|
           else 0) ∂P) ≤
            (n : ℝ≥0∞) *
              (∫⁻ x, ENNReal.ofReal (min (1 : ℝ) |x|) ∂levyMeasure)) := by
  haveI := hlevyMeasure.sigmaFinite
  obtain ⟨A, mA, M, K, Z, hprob, hd⟩ :=
    ProbabilityTheory.exists_isPoissonPointFamily ((volume : Measure ℝ).prod levyMeasure)
  letI : MeasurableSpace A := mA
  letI : IsProbabilityMeasure M := hprob
  let J := ProbabilityTheory.levyJumpPath hd hlevyMeasure (-a)
  refine ⟨A, mA, M, J, hprob,
    ProbabilityTheory.isLevyProcess_levyJumpPath hd hlevyMeasure (-a),
    (fun t => ProbabilityTheory.measurable_levyJumpPath hd hlevyMeasure (-a) t), ?_, ?_⟩
  · intro t ξ
    have hChar := ProbabilityTheory.charFun_map_levyJumpPath hd hlevyMeasure (-a) t ξ
    rw [ProbabilityTheory.LevyKhintchineTriple.exponent_def] at hChar
    simp only [NNReal.coe_zero, Complex.ofReal_zero, zero_mul, zero_div, sub_zero] at hChar
    convert hChar using 1 <;> congr 1 <;> push_cast <;> ring
  · exact Kyprianou.Ch02.levyPoissonPathSmallJumpMassMeanBoundV1
      M levyMeasure K Z hd hlevyMeasure (-a)
