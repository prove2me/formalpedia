-- Prove2me | solution 1 for Kyprianou.Ch02.levyCanonicalSmallJumpMassModelV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:10:11.444664+00:00
-- url     : https://prove2.me/submissions/0240bfc2-cf2c-4d08-a268-78050e8c7c62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_levyCanonicalPureJumpBoundedModelV1
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_Kyprianou_Ch02_levyGaussianExtensionOfBoundedJumpModelV1
open MeasureTheory ProbabilityTheory Complex Function
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    : ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ (t : ℝ≥0) (ξ : ℝ),
          charFun (P.map (X t)) ξ =
            Complex.exp ((((t : ℝ) : ℂ)) *
              Kyprianou.Ch01.levyTripleExponent
                ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) ∧
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
  obtain ⟨A, mA, M, J, hprob, hJ, hJm, hJchar, hJbound⟩ :=
    Kyprianou.Ch02.levyCanonicalPureJumpBoundedModelV1 a levyMeasure hlevyMeasure
  letI : MeasurableSpace A := mA
  letI : IsProbabilityMeasure M := hprob
  exact Kyprianou.Ch02.levyGaussianExtensionOfBoundedJumpModelV1
    a σ levyMeasure hlevyMeasure M J hJ hJm hJchar hJbound
