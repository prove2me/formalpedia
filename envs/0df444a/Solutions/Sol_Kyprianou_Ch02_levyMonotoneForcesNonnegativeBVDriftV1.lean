-- Prove2me | solution 1 for Kyprianou.Ch02.levyMonotoneForcesNonnegativeBVDriftV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:05:12.793488+00:00
-- url     : https://prove2.me/submissions/98b4ac91-54cd-4e09-8568-77da1603b14e

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_levyMonotoneMarginalProbabilityFamilyV1
import Theorems.Thm_Kyprianou_Ch02_canonicalMarginalSmallTimeDataV2
import Theorems.Thm_Kyprianou_Ch02_positiveSmallTimeFirstMomentBoundV1
import Theorems.Thm_Kyprianou_Ch02_positiveJumpDriftFromSmallTimeBoundV1
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
    (hm : ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω))
    (hσ : σ = 0)
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|) levyMeasure)
    (hsupport : levyMeasure (Set.Iio (0 : ℝ)) = 0) :
    0 ≤ -a - ∫ x in Set.Ioo (0 : ℝ) 1, x ∂levyMeasure := by
  obtain ⟨M, hT, hM⟩ :=
    Kyprianou.Ch02.levyMonotoneMarginalProbabilityFamilyV1
      a σ levyMeasure hlevyMeasure P X hX hchar hm
  let T : ProbabilityTheory.LevyKhintchineTriple := ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩
  obtain ⟨r, b, v, ts, hr, hnull, ht, hb, hv, hd, hvar, hjump⟩ :=
    Kyprianou.Ch02.canonicalMarginalSmallTimeDataV2 M T hT
  have hr0 : 0 < r := by linarith [hr.1]
  obtain ⟨hi, hbound⟩ := Kyprianou.Ch02.positiveSmallTimeFirstMomentBoundV1
    M levyMeasure hlevyMeasure hM r b hr0 hr.2 ts hb hjump
  exact Kyprianou.Ch02.positiveJumpDriftFromSmallTimeBoundV1
    T hsupport r b hr0 hr.2 hi hbound hd
