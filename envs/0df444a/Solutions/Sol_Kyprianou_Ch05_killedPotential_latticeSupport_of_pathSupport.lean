-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_latticeSupport_of_pathSupport
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:26:45.385597+00:00
-- url     : https://prove2.me/submissions/24370832-349b-43dc-977c-674a2b534b3e

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
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
  (∀ h : Real, 0 < h →
    (∀ t : NNReal, P {omega : Omega | Y t omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} = 0) →
    ∀ q : Real, 0 ≤ q →
      ((U q).restrict (Set.Ioi (0 : Real))) {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0) := by
  intro h hh hPath q hq
  have hmeas : MeasurableSet {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := by
    have heq : {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = ⋂ n : Int, ({(n : Real) * h} : Set Real)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_compl_iff,
        Set.mem_singleton_iff]
    rw [heq]
    exact MeasurableSet.iInter (fun n => (measurableSet_singleton _).compl)
  rw [Measure.restrict_apply hmeas]
  obtain ⟨-, hU⟩ := hPotential q hq
  rw [hU _ (hmeas.inter measurableSet_Ioi)]
  have hzero : ∀ t : Real,
      ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)} = 0 := by
    intro t
    have hle : P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩ Set.Ioi (0 : Real)} ≤
        P {omega : Omega | Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h}} :=
      measure_mono (fun omega homega => homega.2.1)
    rw [hPath (Real.toNNReal t)] at hle
    rw [le_antisymm hle bot_le, mul_zero]
  have hae : (fun t : Real => ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ {z : Real | ∀ n : Int, z ≠ (n : Real) * h} ∩
            Set.Ioi (0 : Real)}) =ᵐ[volume.restrict (Set.Ici (0 : Real))] 0 :=
    (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall (fun t _ => hzero t))
  rw [lintegral_congr_ae hae]
  simp
