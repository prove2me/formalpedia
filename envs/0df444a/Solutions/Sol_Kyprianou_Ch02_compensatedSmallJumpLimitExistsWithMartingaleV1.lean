-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedSmallJumpLimitExistsWithMartingaleV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:46:31.191795+00:00
-- url     : https://prove2.me/submissions/97fb3bbe-1271-47d0-9193-2bf6e565e29d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpUniformLimitExistsV1
import Theorems.Thm_Kyprianou_Ch02_completedPoissonFiltrationExistsGeneralV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpMartingaleModificationFromUniformV1
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
      (M 0 = fun _ => 0) ∧
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
  obtain ⟨M₀, hzero, huniform⟩ :=
    Kyprianou.Ch02.compensatedSmallJumpUniformLimitExistsV1
      P levyMeasure hlevyMeasure N
  obtain ⟨ℱ, hℱ⟩ :=
    Kyprianou.Ch02.completedPoissonFiltrationExistsGeneralV1
      P levyMeasure N
  obtain ⟨M, hMzero, hmart, hL2, hae⟩ :=
    Kyprianou.Ch02.compensatedSmallJumpMartingaleModificationFromUniformV1
      P levyMeasure hlevyMeasure N ℱ hℱ M₀ hzero huniform
  refine ⟨M, ℱ, hMzero, hℱ, hmart, hL2, ?_⟩
  intro T hT
  obtain ⟨ε, hanti, hbounds, htend, happrox⟩ := huniform T hT
  refine ⟨ε, hanti, hbounds, htend, ?_⟩
  filter_upwards [happrox, hae] with ω hω heq
  intro δ hδ
  obtain ⟨n₀, hn₀⟩ := hω δ hδ
  refine ⟨n₀, ?_⟩
  intro n hn t ht
  simpa only [heq t] using hn₀ n hn t ht
