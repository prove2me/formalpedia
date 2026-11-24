-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteMarkWindowTimeSlicesAtMostOneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:57:25.056321+00:00
-- url     : https://prove2.me/submissions/902189a6-d69a-4132-8059-5ee87d5bc3c5

import Theorems.Thm_Kyprianou_Ch02_prmBadTimeSliceMeasureGridBoundV1
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
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (A : Set ℝ) (hA : MeasurableSet A) (hfin : ν A < ⊤) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ A) ≤ 1 := by
  let D : Set Ω := {ω | ¬ ∀ t : ℝ≥0, 0 < t → t ≤ T →
    N.N ω ({(t : ℝ)} ×ˢ A) ≤ 1}
  rw [ae_iff]
  change P D = 0
  apply (measureReal_eq_zero_iff (measure_ne_top P D)).1
  by_contra hne
  have hpos : 0 < P.real D := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (((T : ℝ) * (ν A).toReal)^2 / P.real D)
  have hlt := (div_lt_iff₀ hpos).1 hn
  have hb := Kyprianou.Ch02.prmBadTimeSliceMeasureGridBoundV1 P ν N A hA hfin T n
  have hle := (le_div_iff₀ (by positivity : 0 < ((n+1 : ℕ) : ℝ))).1 hb
  change P.real D * ((n+1 : ℕ) : ℝ) ≤ _ at hle
  push_cast at hle
  nlinarith
