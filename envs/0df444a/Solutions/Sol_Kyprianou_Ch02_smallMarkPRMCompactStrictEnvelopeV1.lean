-- Prove2me | solution 1 for Kyprianou.Ch02.smallMarkPRMCompactStrictEnvelopeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:55:28.614277+00:00
-- url     : https://prove2.me/submissions/a8d31e4a-8f38-47c9-bd3d-0ffb3949de0a

import Theorems.Thm_Kyprianou_Ch02_smallJumpCompactMarkSupportCapV1
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
    (hν : ProbabilityTheory.IsLevyMeasure ν) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      N.N ω (Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | c < |x| ∧ |x| < 1}) = 0  := by
  exact Kyprianou.Ch02.smallJumpCompactMarkSupportCapV1 P ν N hν T
