-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageZero_consequence3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:06:51.34408+00:00
-- url     : https://prove2.me/submissions/0d6a9d19-67a7-44b8-9384-33a81f65ac40

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_zeroRoot_impliesPsiNonneg
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_psiNonneg_impliesZeroRoot
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      ((phi = 0) <-> (forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta)) := by
  refine fun phi hRoot => ?_
  constructor
  · exact Kyprianou.Ch03.firstPassageZero_zeroRoot_impliesPsiNonneg
      P F L hNotDecreasing phi hRoot
  · exact Kyprianou.Ch03.firstPassageZero_psiNonneg_impliesZeroRoot
      P F L hNotDecreasing phi hRoot
