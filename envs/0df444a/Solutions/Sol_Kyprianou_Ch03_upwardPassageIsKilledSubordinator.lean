-- Prove2me | solution 1 for Kyprianou.Ch03.upwardPassageIsKilledSubordinator
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:49:31.273618+00:00
-- url     : https://prove2.me/submissions/38e55cfa-4526-4be2-878c-1193708df830
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_maximalRootExistence
import Theorems.Thm_Kyprianou_Ch03_killedSubordinator_givenMaximalRoot
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
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
      exists (Omega2 : Type) (m2 : MeasurableSpace Omega2),
        letI : MeasurableSpace Omega2 := m2
        exists (Q : Measure Omega2) (hQ : IsProbabilityMeasure Q),
          letI : IsProbabilityMeasure Q := hQ
          exists (S : NNReal -> Omega2 -> Real)
                 (zeta : Omega2 -> WithTop NNReal),
            IsSubordinator Q S ∧
            Indep
              (MeasurableSpace.comap zeta
                (inferInstance : MeasurableSpace (WithTop NNReal)))
              (MeasurableSpace.comap
                (fun omega : Omega2 => fun x : NNReal => S x omega)
                (inferInstance : MeasurableSpace (NNReal -> Real)))
              Q ∧
            (forall x : NNReal,
              (Q {omega : Omega2 |
                (x : WithTop NNReal) < zeta omega}).toReal =
                  Real.exp (-phi * (x : Real))) ∧
            (phi = 0 ->
              (Q {omega : Omega2 | zeta omega = ⊤}).toReal = 1) ∧
            (0 < phi ->
              (Q {omega : Omega2 | zeta omega != ⊤}).toReal = 1) ∧
            Measure.map
              (fun omega : Omega =>
                fun x : NNReal =>
                  firstHittingTime L.X (Set.Ioi (x : Real)) omega) P =
            Measure.map
              (fun omega : Omega2 =>
                fun x : NNReal =>
                  if (x : WithTop NNReal) < zeta omega
                  then (Real.toNNReal (S x omega) : WithTop NNReal)
                  else ⊤) Q  := by
  obtain ⟨phi, hpos, hroot, hmax⟩ :=
    Kyprianou.Ch03.firstPassageZero_maximalRootExistence
      P F L hNotDecreasing
  refine ⟨phi, hpos, hroot, hmax, ?_⟩
  exact Kyprianou.Ch03.killedSubordinator_givenMaximalRoot
    P F L hNotDecreasing phi ⟨hpos, hroot, hmax⟩
