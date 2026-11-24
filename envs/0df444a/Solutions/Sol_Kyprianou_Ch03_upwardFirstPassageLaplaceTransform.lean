-- Prove2me | solution 1 for Kyprianou.Ch03.upwardFirstPassageLaplaceTransform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:12:22.181646+00:00
-- url     : https://prove2.me/submissions/e4ad6971-e08a-4447-ad6d-a79db5972fdd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_firstPassageTransform_consequence1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Filter
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
    forall (q : Real), 0 <= q ->
      exists phi : Real,
        0 <= phi ∧ L.ψ phi = q ∧
        (forall theta : Real, 0 <= theta ->
          L.ψ theta = q -> theta <= phi) ∧
        (forall (x : Real), 0 <= x ->
          forall (finiteTime : Omega -> NNReal),
            (forall omega,
              firstHittingTime L.X (Set.Ioi x) omega != ⊤ ->
                firstHittingTime L.X (Set.Ioi x) omega =
                  (finiteTime omega : WithTop NNReal)) ->
            (∫ omega,
              if firstHittingTime L.X (Set.Ioi x) omega = ⊤
              then (0 : Real)
              else Real.exp (-q * (finiteTime omega : Real)) ∂P) =
              Real.exp (-phi * x)) := by
  refine fun q hq => ?_
  rcases Kyprianou.Ch03.firstPassageTransform_maximalRootExistence P F L hNotDecreasing q hq with ⟨phi, hnonneg, hroot, hmax⟩
  have hprops : (0 <= phi ∧ L.ψ phi = q ∧
      (∀ theta : Real, 0 <= theta -> L.ψ theta = q -> theta <= phi)) :=
    ⟨hnonneg, hroot, hmax⟩
  refine ⟨phi, hnonneg, hroot, hmax, ?_⟩
  exact Kyprianou.Ch03.firstPassageTransform_consequence1 P F L hNotDecreasing q hq phi hprops


