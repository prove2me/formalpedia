-- Prove2me | solution 2 for Kyprianou.smallJumpLimitCadlagCorrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:36:06.210563+00:00
-- url     : https://prove2.me/submissions/0de83211-d4a6-4571-b512-bc047caf2212

import Theorems.Thm_Kyprianou_Ch02_smallJumpLimitStochasticUniformCoreV1
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
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

open Kyprianou
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      ProbabilityTheory.IsLevyProcess M P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ᵐ ω ∂P,
        (∀ t : ℝ≥0,
          ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
        ∀ t : ℝ≥0, 0 < t →
          ∃ l : ℝ,
            Tendsto (fun s => M s ω)
              (nhdsWithin t (Set.Iio t)) (nhds l)) ∧
      (∀ᵐ ω ∂P,
        Set.Countable {t : ℝ≥0 |
          ¬ ContinuousAt (fun s => M s ω) t}) ∧
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ)
      := by
  rcases Kyprianou.Ch02.smallJumpLimitStochasticUniformCoreV1
      P levyMeasure hlevyMeasure N with
    ⟨M, ℱ, hlevy, hfil, hmart, hlp, huniform⟩
  have hpaths : ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0,
        ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t) ∧
      ∀ t : ℝ≥0, 0 < t →
        ∃ l : ℝ, Tendsto (fun s => M s ω)
          (nhdsWithin t (Set.Iio t)) (nhds l) := by
    filter_upwards [hlevy.cadlag_ae] with ω hcad
    constructor
    · intro t
      exact (hcad t).1
    · intro t _
      exact (hcad t).2
  have hcount : ∀ᵐ ω ∂P,
      Set.Countable {t : ℝ≥0 | ¬ ContinuousAt (fun s => M s ω) t} := by
    filter_upwards [hpaths] with ω hω
    exact Kyprianou.Ch02.cadlagNNRealDiscontinuitiesCountableV1
      (fun s => M s ω) hω.1 hω.2
  exact ⟨M, ℱ, hlevy, hfil, hmart, hlp, hpaths, hcount, huniform⟩
