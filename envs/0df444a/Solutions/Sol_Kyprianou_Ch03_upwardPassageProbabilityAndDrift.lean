-- Prove2me | solution 1 for Kyprianou.Ch03.upwardPassageProbabilityAndDrift
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:12:47.137063+00:00
-- url     : https://prove2.me/submissions/a264f3a8-3049-4f67-ba93-202368f538fc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence2
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence3
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence4
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
    exists phi : Real,
      0 <= phi ∧ L.ψ phi = 0 ∧
      (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi) ∧
      (forall x : Real, 0 <= x ->
        forall finiteTime : Omega -> NNReal,
          (forall omega,
            firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
              firstHittingTime L.X (Set.Ioi x) omega =
                (finiteTime omega : WithTop NNReal)) ->
          (P {omega : Omega |
            firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal =
              Real.exp (-phi * x)) ∧
      (forall x : Real, 0 < x ->
        ((P {omega : Omega |
          firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal = 1
          <-> phi = 0)) ∧
      ((phi = 0) <-> (forall theta : Real, 0 <= theta ->
        0 <= L.ψ theta)) ∧
      (Integrable (L.X 1) P ->
        ((phi = 0) <-> 0 <= (∫ omega, L.X 1 omega ∂P))) := by
  rcases Kyprianou.Ch03.firstPassageZero_maximalRootExistence P F L hNotDecreasing with ⟨phi, hnonneg, hroot, hmax⟩
  have hprops : (0 <= phi ∧ L.ψ phi = 0 ∧
      (∀ theta : Real, 0 <= theta -> L.ψ theta = 0 -> theta <= phi)) :=
    ⟨hnonneg, hroot, hmax⟩
  refine ⟨phi, hnonneg, hroot, hmax, ?_, ?_, ?_, ?_⟩
  · exact Kyprianou.Ch03.firstPassageZero_consequence1 P F L hNotDecreasing phi hprops
  · exact Kyprianou.Ch03.firstPassageZero_consequence2 P F L hNotDecreasing phi hprops
  · exact Kyprianou.Ch03.firstPassageZero_consequence3 P F L hNotDecreasing phi hprops
  · exact Kyprianou.Ch03.firstPassageZero_consequence4 P F L hNotDecreasing phi hprops


