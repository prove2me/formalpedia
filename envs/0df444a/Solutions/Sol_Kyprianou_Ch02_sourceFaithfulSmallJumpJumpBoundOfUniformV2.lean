-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulSmallJumpJumpBoundOfUniformV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:22:20.150246+00:00
-- url     : https://prove2.me/submissions/80431793-1cc2-4413-bbc4-c1cb6462ef51

import Theorems.Thm_Kyprianou_Ch02_smallJumpBandsCommonStrictJumpCapV1
import Theorems.Thm_Kyprianou_Ch02_uniformLimitStrictJumpCapV1
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
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      ∀ l : ℝ,
        Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds l) →
        (M t ω ≠ l → |M t ω - l| < 1)
 := by
  have hh (k : ℕ) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ (k : ℝ≥0) + 1 →
      ∀ l : ℝ, Tendsto (fun s => M s ω) (nhdsWithin t (Set.Iio t)) (nhds l) →
        |M t ω - l| < 1 := by
    let T : ℝ≥0 := (k : ℝ≥0) + 1
    have hT : 0 < T := by positivity
    obtain ⟨ε, _, hε, _, hu⟩ := huniform T hT
    have hb := Kyprianou.Ch02.smallJumpBandsCommonStrictJumpCapV1
      P levyMeasure hlevyMeasure N ε hε T
    filter_upwards [hu, hb] with ω hω hcap
    obtain ⟨c, hc, hbc⟩ := hcap
    intro t ht htT l hl
    exact Kyprianou.Ch02.uniformLimitStrictJumpCapV1
      (fun n s => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) s ω)
      (fun s => M s ω) T c hc hω hbc t ht htT l hl
  have hall := (ae_all_iff).mpr hh
  filter_upwards [hall] with ω hω
  intro t ht l hl _
  obtain ⟨k, hk⟩ := exists_nat_gt t
  exact hω k t ht (hk.le.trans (le_add_of_nonneg_right zero_le_one)) l hl
