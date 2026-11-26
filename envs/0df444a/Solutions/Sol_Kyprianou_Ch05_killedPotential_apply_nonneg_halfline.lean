-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_apply_nonneg_halfline
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:50:43.344745+00:00
-- url     : https://prove2.me/submissions/5ddeb159-8f44-451f-920b-bf304911fcec

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
  (∀ q : Real, 0 ≤ q → (U q) (Set.Iio (0 : Real)) = 0) := by
  intro q hq
  obtain ⟨-, hU⟩ := hPotential q hq
  rw [hU _ measurableSet_Iio]
  have hstart : ∀ omega : Omega, Y 0 omega = 0 :=
    fun omega => congrFun hKilled.1.1.start_zero omega
  have hnonneg : ∀ᵐ omega : Omega ∂P, ∀ s : NNReal, 0 ≤ Y s omega := by
    filter_upwards [hKilled.1.2] with omega hm s
    calc (0 : Real) = Y 0 omega := (hstart omega).symm
    _ ≤ Y s omega := hm bot_le
  have hzero : ∀ t : Real,
      ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ Set.Iio (0 : Real)} = 0 := by
    intro t
    have hnull : P {omega : Omega | ¬ (0 ≤ Y (Real.toNNReal t) omega)} = 0 := by
      apply measure_mono_null _ (MeasureTheory.ae_iff.mp hnonneg)
      intro omega homega hall
      exact homega (hall (Real.toNNReal t))
    have hP : P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ Set.Iio (0 : Real)} = 0 := by
      apply measure_mono_null _ hnull
      intro omega homega
      exact not_le.mpr homega.2
    rw [hP, mul_zero]
  have hae : (fun t : Real => ENNReal.ofReal (Real.exp (-q * t)) *
        P {omega : Omega | (Real.toNNReal t : WithTop NNReal) < death omega ∧
          Y (Real.toNNReal t) omega ∈ Set.Iio (0 : Real)}) =ᵐ[volume.restrict (Set.Ici (0 : Real))] 0 :=
    (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall (fun t _ => hzero t))
  rw [lintegral_congr_ae hae]
  simp
