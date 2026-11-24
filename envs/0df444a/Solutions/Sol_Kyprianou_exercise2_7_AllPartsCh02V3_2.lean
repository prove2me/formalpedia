-- Prove2me | solution 2 for Kyprianou.exercise2_7_AllPartsCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:16:48.339378+00:00
-- url     : https://prove2.me/submissions/fe610524-c918-43ff-8efc-f05886230b33
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_exercise27JumpTailProbabilityV1
import Theorems.Thm_Kyprianou_Ch02_exercise27ContinuousPathsV1
import Theorems.Thm_Kyprianou_Ch02_exercise27PiecewiseLinearV1
import Theorems.Thm_Kyprianou_Ch02_exercise27DenseDiscontinuitiesV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
    (a : ℝ) (σ : ℝ≥0) (ν : Measure ℝ)
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, ν, hν⟩ ξ))
    :
    let piecewiseLinear : (ℝ≥0 → ℝ) → Prop := fun f =>
      ∃ (T : ℕ → ℝ≥0), T 0 = 0 ∧ StrictMono T ∧
        Tendsto T atTop atTop ∧
        ∀ n : ℕ, ∃ (slope intercept : ℝ),
          ∀ t : ℝ≥0, T n ≤ t → t < T (n + 1) →
            f t = slope * (t : ℝ) + intercept
    (∀ (t : ℝ≥0) (threshold : ℝ), 0 < threshold →
      P {ω | ∃ s : ℝ≥0, 0 < s ∧ s ≤ t ∧
        ∃ l : ℝ,
          Tendsto (fun u => X u ω)
            (nhdsWithin s (Set.Iio s)) (nhds l) ∧
          threshold < |X s ω - l|} =
      ENNReal.ofReal (1 -
        Real.exp (-(t : ℝ) *
          (ν {x : ℝ | threshold < |x|}).toReal))) ∧
    ((∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) ↔
      ν = 0) ∧
    ((∀ᵐ ω ∂P, piecewiseLinear (fun t => X t ω)) ↔
      σ = 0 ∧ ν Set.univ < ⊤) ∧
    (ν Set.univ = ⊤ →
      ∀ᵐ ω ∂P,
        closure {t : ℝ≥0 |
          ¬ ContinuousAt (fun s : ℝ≥0 => X s ω) t} =
          Set.univ)
      := by
  dsimp only
  exact ⟨
    Kyprianou.Ch02.exercise27JumpTailProbabilityV1 a σ ν hν P X hX hchar,
    Kyprianou.Ch02.exercise27ContinuousPathsV1 a σ ν hν P X hX hchar,
    Kyprianou.Ch02.exercise27PiecewiseLinearV1 a σ ν hν P X hX hchar,
    Kyprianou.Ch02.exercise27DenseDiscontinuitiesV1 a σ ν hν P X hX hchar⟩
