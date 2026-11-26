-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_atom_sq_le_cesaro_chf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T04:14:44.028602+00:00
-- url     : https://prove2.me/submissions/acf2646e-1dbb-4876-971f-4de408f94337
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_chf_formula
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_atom_sq_le_cesaro_chfAbs
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
  (∀ t : NNReal, 0 < t → ∀ x : Real, ∀ ε : ENNReal, 0 < ε →
    ∃ U0 : Real, ∀ U : Real, U0 ≤ U →
      (P {omega : Omega | Y t omega = x})^2 ≤ (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal (Real.exp (-2 * (t : Real) * (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε) := by
  intro t ht x ε hε
  obtain ⟨U0, hU0⟩ := Kyprianou.Ch05.killedSubordinator_atom_sq_le_cesaro_chfAbs
    P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential t ht x ε hε
  refine ⟨U0, fun V hV => ?_⟩
  have hpt : ∀ u : Real,
      ENNReal.ofReal ((∫ omega, Real.cos (u * Y t omega) ∂P)^2 +
          (∫ omega, Real.sin (u * Y t omega) ∂P)^2)
        = ENNReal.ofReal (Real.exp (-2 * (t : Real) *
            (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal)) := by
    intro u
    obtain ⟨hcos, hsin⟩ := Kyprianou.Ch05.killedSubordinator_chf_formula
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential t u
    rw [hcos, hsin]
    congr 1
    have key : ∀ (E A : Real),
        (E * Real.cos A)^2 + (E * Real.sin A)^2 = E^2 := by
      intro E A
      have h1 : (E * Real.cos A)^2 + (E * Real.sin A)^2
          = E^2 * (Real.cos A ^ 2 + Real.sin A ^ 2) := by ring
      rw [h1, Real.cos_sq_add_sin_sq, mul_one]
    rw [key, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hlint : (∫⁻ u in Set.Icc (0 : Real) V,
        ENNReal.ofReal ((∫ omega, Real.cos (u * Y t omega) ∂P)^2 +
          (∫ omega, Real.sin (u * Y t omega) ∂P)^2) ∂volume)
      = (∫⁻ u in Set.Icc (0 : Real) V,
          ENNReal.ofReal (Real.exp (-2 * (t : Real) *
            (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (1 - Real.cos (u * y)) ∂Pi).toReal))
          ∂volume) :=
    MeasureTheory.lintegral_congr hpt
  exact (hU0 V hV).trans_eq (by rw [hlint])
