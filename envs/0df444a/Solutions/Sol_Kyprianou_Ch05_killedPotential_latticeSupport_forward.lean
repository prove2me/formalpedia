-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_latticeSupport_forward
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:21:36.11363+00:00
-- url     : https://prove2.me/submissions/5d9229c6-5317-47ff-aff9-7c4ddb529c03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_path_latticeSupport_of_latticePi_driftZero
import Theorems.Thm_Kyprianou_Ch05_killedPotential_latticeSupport_of_pathSupport
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
  (Pi (Set.Ioi (0 : Real)) < ⊤ → d = 0 →
    ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
      ∀ q : Real, 0 ≤ q →
        ((U q).restrict (Set.Ioi (0 : Real))) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0) := by
  intro hFin hd h hh hPi q hq
  refine Kyprianou.Ch05.killedPotential_latticeSupport_of_pathSupport
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential h hh ?_ q hq
  intro t
  have hae := Kyprianou.Ch05.killedSubordinator_path_latticeSupport_of_latticePi_driftZero
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hd h hh hPi t
  rw [ae_iff] at hae
  apply measure_mono_null _ hae
  intro omega homega
  simp only [Set.mem_setOf_eq] at homega ⊢
  push_neg
  exact homega
