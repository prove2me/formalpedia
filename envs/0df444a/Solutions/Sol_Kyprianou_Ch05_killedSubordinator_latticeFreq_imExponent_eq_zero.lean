-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_latticeFreq_imExponent_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T04:16:47.237799+00:00
-- url     : https://prove2.me/submissions/77ea00ba-7d27-4e4a-ad87-84851687bef7

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
  (∀ h : Real, 0 < h → Pi {z : Real | ∀ n : Int, z ≠ (n : Real) * h} = 0 →
    (∫ x in Set.Ioi (0 : Real), Real.sin ((2 * Real.pi / h) * x) ∂Pi) = 0) := by
  intro h hh hPi
  obtain ⟨heta, hd, hA, hB, hPhi⟩ := hTriplet
  have haePi : ∀ᵐ x ∂Pi, ∃ n : Int, x = (n : Real) * h := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : Real | ¬ ∃ n : Int, x = (n : Real) * h} =
        {z : Real | ∀ n : Int, z ≠ (n : Real) * h} := by
      ext x
      simp only [Set.mem_setOf_eq, not_exists, ne_eq]
    rw [hset]
    exact hPi
  have hae0 : ∀ᵐ x ∂(Pi.restrict (Set.Ioi (0 : Real))),
      Real.sin ((2 * Real.pi / h) * x) = 0 := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards [haePi] with x hx _
    obtain ⟨n, hn⟩ := hx
    rw [hn]
    have e : (2 * Real.pi / h) * ((n : Real) * h) = (n : Real) * (2 * Real.pi) := by
      field_simp
    have e2 : (n : Real) * (2 * Real.pi) = ((2 * n : Int) : Real) * Real.pi := by
      push_cast
      ring
    rw [e, e2, Real.sin_int_mul_pi]
  exact integral_eq_zero_of_ae hae0
