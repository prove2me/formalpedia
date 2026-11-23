-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedSmallJumpMartingaleModificationFromUniformV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T20:49:02.721331+00:00
-- url     : https://prove2.me/submissions/ebf6a25d-326c-496c-bb96-b7cc2e06f9e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpStronglyAdaptedVersionOfUniformLimitV1
import Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpStrongAdaptedL2MartingaleV1
import Theorems.Thm_Kyprianou_Ch02_compensatedBandL2MartingaleFixedCompletedV1
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
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P levyMeasure N ℱ)
    (M₀ : ℝ≥0 → Ω → ℝ)
    (hzero : M₀ 0 = fun _ => 0)
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
                    M₀ t ω| < δ)
  ) :
    ∃ (M : ℝ≥0 → Ω → ℝ),
      (M 0 = fun _ => 0) ∧
      MeasureTheory.Martingale M ℱ P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M t ω = M₀ t ω)
    := by
  obtain ⟨M, hMzero, hadapt, hae⟩ :=
    Kyprianou.Ch02.compensatedSmallJumpStronglyAdaptedVersionOfUniformLimitV1
      P levyMeasure hlevyMeasure N ℱ hℱ M₀ hzero huniform
  have hband : ∀ ε : ℝ, 0 < ε → ε < 1 →
      MeasureTheory.Martingale
        (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε) ℱ P ∧
      ∀ t : ℝ≥0,
        MemLp (Kyprianou.compensatedSmallJumpBand P levyMeasure N ε t) 2 P := by
    intro ε hε hε1
    exact Kyprianou.Ch02.compensatedBandL2MartingaleFixedCompletedV1
      P levyMeasure hlevyMeasure N ℱ hℱ ε hε hε1
  have huniformM :
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
    intro T hT
    obtain ⟨ε, hanti, hbounds, htend, happrox⟩ := huniform T hT
    refine ⟨ε, hanti, hbounds, htend, ?_⟩
    filter_upwards [happrox, hae] with ω hω heq
    intro δ hδ
    obtain ⟨n₀, hn₀⟩ := hω δ hδ
    refine ⟨n₀, ?_⟩
    intro n hn t ht
    simpa only [heq t] using hn₀ n hn t ht
  obtain ⟨hmart, hL2⟩ :=
    Kyprianou.Ch02.compensatedSmallJumpStrongAdaptedL2MartingaleV1
      P levyMeasure hlevyMeasure N ℱ hℱ M hMzero huniformM hadapt hband
  exact ⟨M, hMzero, hmart, hL2, hae⟩
