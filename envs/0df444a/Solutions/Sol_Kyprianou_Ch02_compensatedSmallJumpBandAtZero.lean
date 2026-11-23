-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedSmallJumpBandAtZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:57:44.226898+00:00
-- url     : https://prove2.me/submissions/b61c5f9d-4484-4f22-9160-2c855c359a9b

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
open MeasureTheory ProbabilityTheory
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (levyMeasure : Measure ℝ) [SigmaFinite levyMeasure]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P levyMeasure)
    (ε : ℝ) (ω : Ω) :
    Kyprianou.compensatedSmallJumpBand P levyMeasure N ε 0 ω = 0 := by
  simp [Kyprianou.compensatedSmallJumpBand]
