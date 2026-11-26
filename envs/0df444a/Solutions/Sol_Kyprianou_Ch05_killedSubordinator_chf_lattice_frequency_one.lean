-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_chf_lattice_frequency_one
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T04:18:18.805643+00:00
-- url     : https://prove2.me/submissions/e57d26dd-af55-4f47-8554-a3cb364d224d

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_chf_formula
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_latticeFreq_reExponent_eq_zero
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_latticeFreq_imExponent_eq_zero
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
  (d = 0 → ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
    ∀ t : NNReal,
      (∫ omega, Real.cos ((2 * Real.pi / h) * Y t omega) ∂P) = 1 ∧
      (∫ omega, Real.sin ((2 * Real.pi / h) * Y t omega) ∂P) = 0) := by
  intro hd h hh hPi t
  obtain ⟨hcos, hsin⟩ := Kyprianou.Ch05.killedSubordinator_chf_formula
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential t (2 * Real.pi / h)
  have hR : (∫⁻ x in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos ((2 * Real.pi / h) * x)) ∂Pi) = 0 :=
    Kyprianou.Ch05.killedSubordinator_latticeFreq_reExponent_eq_zero
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential h hh hPi
  have hS : (∫ x in Set.Ioi (0 : Real), Real.sin ((2 * Real.pi / h) * x) ∂Pi) = 0 :=
    Kyprianou.Ch05.killedSubordinator_latticeFreq_imExponent_eq_zero
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential h hh hPi
  refine ⟨?_, ?_⟩
  · rw [hcos, hR, hS, hd]
    simp
  · rw [hsin, hR, hS, hd]
    simp
