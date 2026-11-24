-- Prove2me | solution 1 for Kyprianou.Ch02.smallJumpBandsCommonStrictJumpCapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:54:01.812673+00:00
-- url     : https://prove2.me/submissions/ad6a8a24-e6bc-402f-b967-5745d8904676

import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkTimeFibresAtMostOneV1
import Theorems.Thm_Kyprianou_Ch02_smallJumpCompactMarkSupportCapV1
import Theorems.Thm_Kyprianou_Ch02_compensatedBandLeftJumpBoundFromFibreEnvelopeV1
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

open Kyprianou
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
      ∀ (n : ℕ) (t : ℝ≥0), 0 < t → t ≤ T →
        ∃ l : ℝ,
          Tendsto (fun s => Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) s ω)
            (nhdsWithin t (Set.Iio t)) (nhds l) ∧
          |Kyprianou.compensatedSmallJumpBand P levyMeasure N (ε n) t ω - l| ≤ c
     := by
  let A (n : ℕ) : Set ℝ := {x | ε n ≤ |x| ∧ |x| < 1}
  have hA (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  have hfin (n : ℕ) : levyMeasure (A n) < ⊤ := by
    have hle : levyMeasure (A n) ≤ levyMeasure {x : ℝ | ε n ≤ |x|} :=
      measure_mono (fun _ hx => hx.1)
    exact lt_of_le_of_lt hle
      (ProbabilityTheory.IsLevyMeasure.measure_setOf_abs_ge_lt_top hlevyMeasure (hε n).1)
  have hwindow (n : ℕ) : LevyStochCalc.Poisson.referenceIntensity levyMeasure
      (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A n) ≠ ⊤ := by
    rw [LevyStochCalc.Poisson.referenceIntensity, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc]
    have hset : Set.Ioc (0 : ℝ) (T : ℝ) ∩ Set.Ici (0 : ℝ) =
        Set.Ioc (0 : ℝ) (T : ℝ) :=
      Set.inter_eq_left.mpr (fun _ hx => hx.1.le)
    rw [hset, Real.volume_Ioc, sub_zero]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin n).ne
  have hcount (n : ℕ) : ∀ᵐ ω ∂P, ∃ k : ℕ,
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A n) = k :=
    N.integer_valued (measurableSet_Ioc.prod (hA n)) (hwindow n)
  have hfib (n : ℕ) := Kyprianou.Ch02.prmFiniteMarkTimeFibresAtMostOneV1
    P levyMeasure N (A n) (hA n) (hfin n) T
  have hcap := Kyprianou.Ch02.smallJumpCompactMarkSupportCapV1
    P levyMeasure N hlevyMeasure T
  filter_upwards [hcap, ae_all_iff.mpr hcount, ae_all_iff.mpr hfib] with ω hc hk hf
  obtain ⟨c, hc0, hc1, henv⟩ := hc
  refine ⟨c, hc1, ?_⟩
  intro n t ht htT
  obtain ⟨k, hkn⟩ := hk n
  have hfinite : N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ A n) < ⊤ := by
    rw [hkn]
    exact ENNReal.natCast_lt_top k
  exact Kyprianou.Ch02.compensatedBandLeftJumpBoundFromFibreEnvelopeV1
    P levyMeasure N (ε n) (hε n).1 (hε n).2 T ω c hc0 hfinite henv (hf n) t ht htT
