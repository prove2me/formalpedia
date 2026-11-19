-- Prove2me | solution 1 for Kyprianou.Ch03.spectrallyNegativePsi_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T21:07:30.123675+00:00
-- url     : https://prove2.me/submissions/5f4d95ca-d8e0-4645-8b75-ef559bc93f34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    L.ψ 0 = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, AvramDividend.Classical.laplaceExponent]
