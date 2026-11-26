-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_firstJump_offLattice_charge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:53:27.927226+00:00
-- url     : https://prove2.me/submissions/ec4539b0-eb27-45a9-be75-a3504a8d2e7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_firstJump_smallTime_charge
import Theorems.Thm_Kyprianou_Ch05_killedPotential_firstJump_integral_lower_bound
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
    ∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0 →
      ∀ q : Real, 0 ≤ q → (U q) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ≠ 0) := by
  intro hFin h hh hPi q hq
  obtain ⟨c, hc, δ, hδ, hcharge⟩ :=
    Kyprianou.Ch05.killedPotential_firstJump_smallTime_charge
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hFin h hh hPi
  have hmeas : MeasurableSet {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := by
    have heq : {z : Real | ∀ n : Int, z ≠ (n : Real) * h} =
        ⋂ n : Int, ({(n : Real) * h} : Set Real)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_singleton_iff]
    rw [heq]
    exact MeasurableSet.iInter (fun n => (measurableSet_singleton _).compl)
  obtain ⟨-, hU⟩ := hPotential q hq
  rw [hU _ hmeas]
  have hKpos : 0 < ENNReal.ofReal (Real.exp (-q * δ)) :=
    ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  have hbound := Kyprianou.Ch05.killedPotential_firstJump_integral_lower_bound
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential h q hq δ c hcharge
  have hne : ENNReal.ofReal (Real.exp (-q * δ)) * c ≠ 0 :=
    mul_ne_zero (ne_of_gt hKpos) (ne_of_gt hc)
  intro hzero
  rw [hzero] at hbound
  exact hne (le_antisymm hbound (bot_le))
