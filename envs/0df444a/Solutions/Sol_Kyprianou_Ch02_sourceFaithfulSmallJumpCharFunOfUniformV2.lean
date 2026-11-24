-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulSmallJumpCharFunOfUniformV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:15:58.471956+00:00
-- url     : https://prove2.me/submissions/b5f315fe-e4b4-4062-ae8b-e272897677b6

import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulCompensatedBandCharFunKLSV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpCharFunFixedTimeLimitV1
import Theorems.Thm_Kyprianou_Ch02_sourceFaithfulSmallJumpExponentBandLimitV1
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

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (M : ℝ≥0 → Ω → ℝ)
    (hM : ProbabilityTheory.IsLevyProcess M P)
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
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map (M t)) ξ =
        Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)
    := by
  intro t ξ
  obtain ⟨ε, _, hε, hzero, hclose⟩ := huniform (t + 1) (by positivity)
  have hfixed : ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ n₀ : ℕ, ∀ n ≥ n₀,
        |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - M t ω| < δ := by
    filter_upwards [hclose] with ω hω
    intro δ hδ
    obtain ⟨n₀, hn₀⟩ := hω δ hδ
    exact ⟨n₀, fun n hn => hn₀ n hn t (le_self_add)⟩
  have hlim := Kyprianou.Ch02.sourceFaithfulSmallJumpCharFunFixedTimeLimitV1
    P levyMeasure hlevyMeasure N M hM ε hε t ξ hfixed
  have hexp := Kyprianou.Ch02.sourceFaithfulSmallJumpExponentBandLimitV1
    levyMeasure hlevyMeasure ε hε hzero t ξ
  have hband := fun n => Kyprianou.Ch02.sourceFaithfulCompensatedBandCharFunKLSV1
    P levyMeasure hlevyMeasure N (ε n) (hε n).1 (hε n).2 t ξ
  exact tendsto_nhds_unique hlim (by simpa only [hband] using hexp)
