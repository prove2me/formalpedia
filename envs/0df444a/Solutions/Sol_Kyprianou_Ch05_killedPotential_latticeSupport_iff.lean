-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_latticeSupport_iff
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:21:36.204731+00:00
-- url     : https://prove2.me/submissions/f9601232-c8d5-4c8d-aae7-10b3cd3215a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_forward
import Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_reverse
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  (Pi (Set.Ioi (0 : Real)) < ⊤ →
     d = 0 →
     ∀ q : Real, 0 ≤ q →
       ∀ h : Real, 0 < h →
         (Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 ↔
          ((U q).restrict (Set.Ioi (0 : Real))) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0)) := by
  intro hFin hd q hq h hh
  constructor
  · intro hPi
    exact Kyprianou.Ch05.killedPotential_latticeSupport_forward
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
      hFin hd h hh hPi q hq
  · intro hU
    exact Kyprianou.Ch05.killedPotential_latticeSupport_reverse
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential
      hFin hd h hh q hq hU
