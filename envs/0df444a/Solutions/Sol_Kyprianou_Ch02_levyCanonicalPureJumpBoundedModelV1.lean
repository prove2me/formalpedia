-- Prove2me | solution 1 for Kyprianou.Ch02.levyCanonicalPureJumpBoundedModelV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:14:20.388279+00:00
-- url     : https://prove2.me/submissions/224c784e-2db5-41ea-9705-7adb05d639b1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_levyCanonicalPureJumpExplicitModelV1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
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
              Kyprianou.Ch01.levyTripleExponent
                ⟨-a, 0, levyMeasure, hlevyMeasure⟩ ξ)) ∧
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
    Kyprianou.Ch02.levyCanonicalPureJumpExplicitModelV1 a levyMeasure hlevyMeasure
  refine ⟨A, mA, M, J, hprob, hJ, hJm, ?_, hJbound⟩
  intro t ξ
  rw [hJchar t ξ]
  congr 1
  dsimp [Kyprianou.Ch01.levyTripleExponent]
  push_cast
  ring
