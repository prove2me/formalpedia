-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedSmallJumpLimitIsLevyOfMartingaleV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:41:54.870591+00:00
-- url     : https://prove2.me/submissions/abaa6c4f-3fd9-4954-a094-fb4a1aee99b3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitHasIndependentIncrementsOfMartingaleV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitHasStationaryIncrementsOfMartingaleV1
import Theorems.Thm_Kyprianou_Ch02_cadlagOfSmallJumpUniformApproxV1
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
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hzero : M 0 = fun _ => 0)
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
    (hmart : MeasureTheory.Martingale M ℱ P)
    (hL2 : ∀ t, MemLp (M t) 2 P)
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
                    M t ω| < δ)
  ) :
    ProbabilityTheory.IsLevyProcess M P
:= by
  have hindep := Kyprianou.Ch02.compensatedSmallJumpUniformLimitHasIndependentIncrementsOfMartingaleV1
    P levyMeasure hlevyMeasure N M ℱ hzero hℱ hmart hL2 huniform
  have hstationary := Kyprianou.Ch02.compensatedSmallJumpUniformLimitHasStationaryIncrementsOfMartingaleV1
    P levyMeasure hlevyMeasure N M ℱ hzero hℱ hmart hL2 huniform
  have hpaths := Kyprianou.Ch02.cadlagOfSmallJumpUniformApproxV1
    P levyMeasure hlevyMeasure N M huniform
  have hcadlag : ∀ᵐ ω ∂P,
      ProbabilityTheory.IsCadlag (fun t => M t ω) := by
    filter_upwards [hpaths] with ω hω
    change ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s => M s ω) (Set.Ici t) t ∧
      ∃ l : ℝ, Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds l)
    intro t
    refine ⟨hω.1 t, ?_⟩
    by_cases ht : 0 < t
    · exact hω.2 t ht
    · have hz : t = 0 := le_antisymm (le_of_not_gt ht) bot_le
      subst t
      exact ⟨0, by simp [Set.Iio_bot, nhdsWithin_empty]⟩
  exact ⟨hzero, hindep, hstationary, hcadlag⟩
