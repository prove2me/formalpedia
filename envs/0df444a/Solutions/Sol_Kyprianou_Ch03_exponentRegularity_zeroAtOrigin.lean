-- Prove2me | solution 1 for Kyprianou.Ch03.exponentRegularity_zeroAtOrigin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T13:21:22.315234+00:00
-- url     : https://prove2.me/submissions/2254cab8-63ca-4ff5-a4eb-d9e0d0b411a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false


theorem solution
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    L.ψ 0 = 0 := by
  simp [AvramDividend.Classical.SpectrallyNegativeLevy.ψ, AvramDividend.Classical.laplaceExponent]

