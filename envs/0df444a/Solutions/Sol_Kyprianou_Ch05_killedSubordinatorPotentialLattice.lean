-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinatorPotentialLattice
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:10:39.489909+00:00
-- url     : https://prove2.me/submissions/9bbb2ae0-07af-4248-afba-a347ce697f17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_atomless_of_infiniteActivity
import Theorems.Thm_Kyprianou_Ch05_killedPotential_nonLattice_of_finiteActivity
import Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_iff
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
  ((Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ q : Real, 0 ≤ q →
      ∀ x : Real, (U q) {x} = 0) ∧
   (Pi (Set.Ioi (0 : Real)) < ⊤ →
     Kyprianou.Ch05.NonLatticeMeasure Pi →
     ∀ q : Real, 0 ≤ q → Kyprianou.Ch05.NonLatticeMeasure (U q)) ∧
   (Pi (Set.Ioi (0 : Real)) < ⊤ →
     d = 0 →
     ∀ q : Real, 0 ≤ q →
       ∀ h : Real, 0 < h →
         (Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 ↔
          ((U q).restrict (Set.Ioi (0 : Real)))
            {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hPi q hq x
    exact Kyprianou.Ch05.killedPotential_atomless_of_infiniteActivity
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi q hq x
  · intro hFin hNL q hq
    exact Kyprianou.Ch05.killedPotential_nonLattice_of_finiteActivity
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hFin hNL q hq
  · intro hFin hd q hq h hh
    exact Kyprianou.Ch05.killedPotential_latticeSupport_iff
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hFin hd q hq h hh
