-- Prove2me | solution 3 for Kyprianou.Ch02.smallJumpLimitStochasticUniformCoreV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:40:12.949416+00:00
-- url     : https://prove2.me/submissions/d7932253-42bb-46d6-a658-767a354b9a53
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_completedPoissonFiltrationExistsGeneralV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitExistsV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpLimitCompletedL2VersionV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitIsLevyV1
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
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure) :
    ∃ (M : ℝ≥0 → Ω → ℝ)
      (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      ProbabilityTheory.IsLevyProcess M P ∧
      Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
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
  rcases Kyprianou.Ch02.completedPoissonFiltrationExistsGeneralV1
      P levyMeasure N with ⟨ℱ, hℱ⟩
  rcases Kyprianou.Ch02.compensatedSmallJumpUniformLimitExistsV1
      P levyMeasure hlevyMeasure N with ⟨M, hz, hu⟩
  rcases Kyprianou.Ch02.compensatedSmallJumpLimitCompletedL2VersionV1
      P levyMeasure hlevyMeasure N ℱ hℱ M hz hu with
      ⟨M', hz', _, hm', hl2', hu'⟩
  have hlevy := Kyprianou.Ch02.compensatedSmallJumpUniformLimitIsLevyV1
    P levyMeasure hlevyMeasure N M' hz' hu'
  exact ⟨M', ℱ, hlevy, hℱ, hm', hl2', hu'⟩
