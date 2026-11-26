-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_path_latticeSupport_of_latticePi_driftZero
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:52:07.450285+00:00
-- url     : https://prove2.me/submissions/bcf797b0-9e85-4805-9dc9-78f3db49b162

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_chf_lattice_frequency_one
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
    ∀ t : NNReal, ∀ᵐ omega : Omega ∂P,
      ∃ n : Int, Y t omega = (n : Real) * h) := by
  intro hd h hh hPi t
  obtain ⟨hcos, -⟩ := Kyprianou.Ch05.killedSubordinator_chf_lattice_frequency_one
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hd h hh hPi t
  have hInt : Integrable (fun omega => Real.cos ((2 * Real.pi / h) * Y t omega)) P := by
    by_contra hni
    rw [MeasureTheory.integral_undef hni] at hcos
    exact zero_ne_one hcos
  have hgint : (∫ omega, (1 - Real.cos ((2 * Real.pi / h) * Y t omega)) ∂P) = 0 := by
    rw [integral_sub (integrable_const 1) hInt, integral_const, hcos]
    simp
  have hgnonneg : (0 : Omega → Real) ≤ᵐ[P]
      (fun omega => 1 - Real.cos ((2 * Real.pi / h) * Y t omega)) :=
    Filter.Eventually.of_forall (fun omega => sub_nonneg.mpr (Real.cos_le_one _))
  have hgi : Integrable (fun omega => 1 - Real.cos ((2 * Real.pi / h) * Y t omega)) P :=
    (integrable_const 1).sub hInt
  have hae : (fun omega => 1 - Real.cos ((2 * Real.pi / h) * Y t omega)) =ᵐ[P] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hgnonneg hgi).mp hgint
  filter_upwards [hae] with omega homega
  have hcos1 : Real.cos ((2 * Real.pi / h) * Y t omega) = 1 := by
    have h9 : (1 : Real) - Real.cos ((2 * Real.pi / h) * Y t omega) = 0 := homega
    linarith [h9]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hcos1
  refine ⟨n, ?_⟩
  have hne : h ≠ 0 := ne_of_gt hh
  have hpi : (2 * Real.pi) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h2 : (2 * Real.pi / h) * Y t omega = (n : Real) * (2 * Real.pi) := hn.symm
  have h5 : (2 * Real.pi / h) * Y t omega = (2 * Real.pi / h) * ((n : Real) * h) := by
    rw [h2]
    field_simp
  exact mul_left_cancel₀ (div_ne_zero hpi hne) h5
