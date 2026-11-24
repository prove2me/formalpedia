-- Prove2me | solution 2 for Kyprianou.Ch02.sourceFaithfulSmallJumpBandsCompactJumpCapV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:53:24.212992+00:00
-- url     : https://prove2.me/submissions/e9f9995d-768f-444c-8c42-0f28536c76bd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Kyprianou_Ch02_prmNearOneWindowStrictMarkCapV1
import Theorems.Thm_Kyprianou_Ch02_prmCompensatedBandJumpCapGivenMarkCutoffV1
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
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n ∧ ε n < 1)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, c < 1 ∧
      ∀ n (t : ℝ≥0), 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - l| ≤ c := by
  have hC := Kyprianou.Ch02.prmNearOneWindowStrictMarkCapV1
    P levyMeasure N hlevyMeasure T
  have hB : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ c : ℝ, 0 ≤ c →
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0 →
      ∀ t : ℝ≥0, 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - l| ≤ c := by
    rw [ae_all_iff]
    intro n
    exact Kyprianou.Ch02.prmCompensatedBandJumpCapGivenMarkCutoffV1
      P levyMeasure N hlevyMeasure (ε n) (hε n).1 (hε n).2 T
  filter_upwards [hC, hB] with ω hw hband
  obtain ⟨c, hc, hc1, hcut⟩ := hw
  exact ⟨c, hc1, fun n t ht htT => hband n c hc hcut t ht htT⟩
