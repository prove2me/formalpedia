-- Prove2me | solution 1 for Kyprianou.Ch02.levyMonotoneForcesPositiveJumpSupportV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:48:20.618899+00:00
-- url     : https://prove2.me/submissions/20655652-d238-4124-b40d-6988b4cb3452

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_levyMonotoneMarginalProbabilityFamilyV1
import Theorems.Thm_Kyprianou_Ch02_canonicalMarginalSmallTimeDataV2
import Theorems.Thm_Kyprianou_Ch02_negativeSupportFromMarginalSmallTimeTestsV2
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hchar : ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (X t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ))
    (hm : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) :
    levyMeasure (Set.Iio (0 : ℝ)) = 0 := by
  obtain ⟨M, hT, hM⟩ :=
    Kyprianou.Ch02.levyMonotoneMarginalProbabilityFamilyV1
      a σ levyMeasure hlevyMeasure P X hX hchar hm
  let T : ProbabilityTheory.LevyKhintchineTriple := ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩
  obtain ⟨r, b, v, ts, hr, hnull, ht, hb, hv, hd, hvar, hjump⟩ :=
    Kyprianou.Ch02.canonicalMarginalSmallTimeDataV2 M T hT
  exact Kyprianou.Ch02.negativeSupportFromMarginalSmallTimeTestsV2
    M levyMeasure hlevyMeasure hM ts hjump
