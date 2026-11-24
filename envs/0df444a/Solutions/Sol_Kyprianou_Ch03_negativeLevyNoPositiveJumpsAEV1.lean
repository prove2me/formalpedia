-- Prove2me | solution 1 for Kyprianou.Ch03.negativeLevyNoPositiveJumpsAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:37:14.029107+00:00
-- url     : https://prove2.me/submissions/f0da6fbb-f1bd-4a69-976c-285d1978fb1f

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_no_positive_jumps
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0) :
    ∀ᵐ omega ∂P, ∀ (t : NNReal) (l : ℝ), 0 < t →
      Tendsto (fun s => X s omega) (nhdsWithin t (Iio t)) (nhds l) →
      X t omega ≤ l := by
  by_cases ha : ∀ᵐ w ∂P, Antitone (fun t : NNReal => X t w)
  · filter_upwards [ha] with w hw
    intro t l ht hl
    haveI : (nhdsWithin t (Iio t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    apply ge_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hw (le_of_lt hs)
  · let D : Kyprianou.Ch08.SpectrallyNegativeModel Omega P :=
      { X := X
        levy := hX
        triplet := T
        characteristic := hLK
        negativeJumps := hNegative
        gaussianCoefficient := Real.sqrt (T.gaussianVariance : ℝ)
        gaussianNonnegative := Real.sqrt_nonneg _
        gaussianVarianceMatch := Real.sq_sqrt (by positivity)
        excludesNegativeSubordinator := ha }
    exact Kyprianou.Ch08.StageB.source_result81_no_positive_jumps Omega P D
