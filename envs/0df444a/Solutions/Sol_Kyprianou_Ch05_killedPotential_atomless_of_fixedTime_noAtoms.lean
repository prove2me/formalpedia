-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_atomless_of_fixedTime_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:26:45.294426+00:00
-- url     : https://prove2.me/submissions/8e28df28-d4e8-4d70-8d15-436c46382f28

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
  ((∀ t : NNReal, 0 < t → ∀ x : Real,
      P {omega : Omega | Y t omega = x} = 0) →
    ∀ q : Real, 0 ≤ q → ∀ x : Real, (U q) {x} = 0) := by
  intro hNo q hq x
  obtain ⟨-, hU⟩ := hPotential q hq
  rw [hU {x} (measurableSet_singleton x)]
  have hzero : ∀ t ∈ Set.Ioi (0 : Real),
      ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ ({x} : Set Real)} = 0 := by
    intro t ht
    have ht0 : (0 : NNReal) < Real.toNNReal t := Real.toNNReal_pos.mpr ht
    have hle : P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ ({x} : Set Real)} ≤
        P {omega : Omega | Y (Real.toNNReal t) omega = x} :=
      measure_mono (fun omega homega => by
        simpa using homega.2)
    rw [hNo (Real.toNNReal t) ht0 x] at hle
    rw [le_antisymm hle bot_le, mul_zero]
  have h0 : ∀ᵐ t ∂(volume : Measure Real), t ≠ (0 : Real) := by
    rw [MeasureTheory.ae_iff]
    simp
  have hae : (fun t : Real => ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ ({x} : Set Real)}) =ᵐ[volume.restrict (Set.Ici (0 : Real))] 0 := by
    refine (ae_restrict_iff' measurableSet_Ici).mpr ?_
    filter_upwards [h0] with t ht0 htIci
    exact hzero t (lt_of_le_of_ne htIci (Ne.symm ht0))
  rw [lintegral_congr_ae hae]
  simp
