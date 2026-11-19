-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageZero_maximalRootExistence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:27:38.048597+00:00
-- url     : https://prove2.me/submissions/e809f6dd-d372-4e4a-9631-b2bfc575e9f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) := by
    exact Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L hNotDecreasing 0 (le_refl 0)

