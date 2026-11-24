-- Prove2me | solution 1 for Kyprianou.Ch02.exercise27ContinuousPathsV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:46:58.535354+00:00
-- url     : https://prove2.me/submissions/3b295c1f-fb1d-4e42-9e3e-3f7f67a8f99b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_Kyprianou_Ch02_exercise27ContinuousPathsOnlyIfV1
import Theorems.Thm_Kyprianou_Ch02_exercise27ContinuousPathsIfV1
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
    ((∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => X t ω)) ↔
      ν = 0) := by
  exact ⟨Kyprianou.Ch02.exercise27ContinuousPathsOnlyIfV1 a σ ν hν P X hX hchar,
    Kyprianou.Ch02.exercise27ContinuousPathsIfV1 a σ ν hν P X hX hchar⟩
