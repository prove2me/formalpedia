-- Prove2me | solution 1 for Kyprianou.Ch02.sourceFaithfulSmallJumpBandsCompactJumpCapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:51:35.273108+00:00
-- url     : https://prove2.me/submissions/308048b1-7bc0-4751-91eb-bb2bb1ebb57a

import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeFibresAtMostOneV1
import Theorems.Thm_Kyprianou_Ch02_smallMarkPRMCompactStrictEnvelopeV1
import Theorems.Thm_Kyprianou_Ch02_compensatedBandLeftJumpBoundFromFibreEnvelopeV1
import Theorems.Thm_Kyprianou_Ch02_smallJumpBandMeasureFiniteV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeRectIntensityFiniteV1
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

open Kyprianou Kyprianou.Ch02

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
  let B (n : ℕ) : Set ℝ := {x | ε n ≤ |x| ∧ |x| < 1}
  have hB (n : ℕ) : MeasurableSet (B n) :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfin (n : ℕ) : levyMeasure (B n) < ⊤ :=
    Kyprianou.Ch02.smallJumpBandMeasureFiniteV1 levyMeasure hlevyMeasure
      (ε n) (hε n).1
  have hfibre := ae_all_iff.2 (fun n : ℕ =>
    Kyprianou.Ch02.prmFiniteMarkTimeFibresAtMostOneV1
      P levyMeasure N (B n) (hB n) (hfin n) T)
  have hmass : ∀ᵐ ω ∂P, ∀ n : ℕ,
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B n) < ⊤ := by
    apply ae_all_iff.2
    intro n
    have hf := Kyprianou.Ch02.prmFiniteMarkTimeRectIntensityFiniteV1
      levyMeasure (B n) (hB n) (hfin n) 0 T
    filter_upwards [N.integer_valued (measurableSet_Ioc.prod (hB n))
      (by simpa using hf)] with ω hω
    obtain ⟨k, hk⟩ := hω
    simp [hk]
  filter_upwards [hfibre, hmass,
    Kyprianou.Ch02.smallMarkPRMCompactStrictEnvelopeV1
      P levyMeasure N hlevyMeasure T] with ω hF hM hE
  obtain ⟨c, hc, hc1, henv⟩ := hE
  refine ⟨c, hc1, fun n t ht htT => ?_⟩
  exact Kyprianou.Ch02.compensatedBandLeftJumpBoundFromFibreEnvelopeV1
    P levyMeasure N (ε n) (hε n).1 (hε n).2 T ω c hc
    (hM n) henv (hF n) t ht htT
