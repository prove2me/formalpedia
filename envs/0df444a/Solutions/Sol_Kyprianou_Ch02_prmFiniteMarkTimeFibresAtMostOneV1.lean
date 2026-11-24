-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteMarkTimeFibresAtMostOneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:56:07.393599+00:00
-- url     : https://prove2.me/submissions/ce7e92b8-5a3d-4554-a504-6f842ec0dc42

import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkWindowTimeSlicesAtMostOneV1
import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t ≤ T →
      N.N ω ({(t : ℝ)} ×ˢ B) ≤ 1 := by
  exact Kyprianou.Ch02.prmFiniteMarkWindowTimeSlicesAtMostOneV1 P ν N B hB hfin T
