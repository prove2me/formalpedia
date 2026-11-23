-- Prove2me | solution 1 for Kyprianou.Ch02.cadlagOfSmallJumpUniformApproxV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:54:31.697422+00:00
-- url     : https://prove2.me/submissions/3ec2e3bb-5533-49d4-977a-a83639a121d5

import Theorems.Thm_Kyprianou_Ch02_cadlagOfUniformSmallJumpBandFromCadlagBandsV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpBandCadlagAEV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou Kyprianou.Ch02
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)) :
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => M s ω)
              (nhdsWithin t (Set.Iio t)) (nhds l))
    := by
  exact Kyprianou.Ch02.cadlagOfUniformSmallJumpBandFromCadlagBandsV1
    P levyMeasure hlevyMeasure N M
    (fun ε hε hε1 =>
      Kyprianou.Ch02.compensatedSmallJumpBandCadlagAEV1
        P levyMeasure hlevyMeasure N ε hε hε1)
    huniform
