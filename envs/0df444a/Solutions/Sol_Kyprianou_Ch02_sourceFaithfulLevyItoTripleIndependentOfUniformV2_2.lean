-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulLevyItoTripleIndependentOfUniformV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:34:40.83181+00:00
-- url     : https://prove2.me/submissions/4586d292-8d0a-4cfc-840a-837aecc88e32

import Theorems.Thm_Kyprianou_Ch02_largeJumpPathMeasurableMarkRegionV1
import Theorems.Thm_Kyprianou_Ch02_smallJumpUniformLimitMarkRegionVersionV1
import Theorems.Thm_Kyprianou_Ch02_levyItoTripleIndependentFromMarkRegionPathsV1
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open scoped Topology

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hM : ProbabilityTheory.IsLevyProcess M P)
    (a : ℝ) (σ : ℝ≥0)
    (B : LevyStochCalc.Brownian.BrownianMotion P)
    (hDrivers : ProbabilityTheory.IndepFun
      (fun ω => fun (t : ℝ) => B.W t ω)
      (fun ω => N.N ω) P)
    (huniform :
      ∀ T : ℝ≥0, 0 < T →
        ∃ ε : ℕ → ℝ,
          StrictAnti ε ∧
          (∀ n, 0 < ε n ∧ ε n < 1) ∧
          Tendsto ε Filter.atTop (nhds 0) ∧
          (∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
            ∃ n₀ : ℕ, ∀ n ≥ n₀,
              ∀ t : ℝ≥0, t ≤ T →
                |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω -
                    M t ω| < δ))
 :
    Kyprianou.IndependentLevyItoComponents P
      (fun (t : ℝ≥0) (ω : Ω) =>
        (σ : ℝ) * B.W (t : ℝ) ω - a * (t : ℝ))
      (Kyprianou.largeJumpProcess P levyMeasure N)
      M
 := by
  obtain ⟨S, hS, hSM⟩ :=
    Kyprianou.Ch02.smallJumpUniformLimitMarkRegionVersionV1
      P levyMeasure hlevyMeasure N M huniform
  have hL := Kyprianou.Ch02.largeJumpPathMeasurableMarkRegionV1
    P levyMeasure hlevyMeasure N
  have h := Kyprianou.Ch02.levyItoTripleIndependentFromMarkRegionPathsV1
    P levyMeasure hlevyMeasure N a σ B hDrivers
    (fun ω t => Kyprianou.largeJumpProcess P levyMeasure N t ω) S hL hS
  unfold Kyprianou.IndependentLevyItoComponents at h ⊢
  refine iIndepFun.congr ?_ h
  intro i
  fin_cases i
  · exact Filter.EventuallyEq.rfl
  · exact Filter.EventuallyEq.rfl
  · simpa using hSM
