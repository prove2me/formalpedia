-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_atom_sq_le_cesaro_chfAbs
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T11:31:59.090006+00:00
-- url     : https://prove2.me/submissions/cbb44f1e-44b6-422b-9cf5-2661735cd417
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_wiener_atom_sq_le_cesaro_measurable
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
      (P {omega : Omega | Y t omega = x})^2 ≤ (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Y t omega) ∂P)^2 + (∫ omega, Real.sin (u * Y t omega) ∂P)^2) ∂volume) * (ENNReal.ofReal U)⁻¹ + ε) := by
  intro t ht x ε hε
  have hAe : AEMeasurable (Y t) P := by
    have hstat := hKilled.1.1.stationary_increments 0 t
    have hm2 : AEMeasurable (ProbabilityTheory.increment Y 0 t) P :=
      hstat.aemeasurable_snd
    have h0 : Y 0 = fun _ => (0 : Real) := hKilled.1.1.start_zero
    have heq : ProbabilityTheory.increment Y 0 t = Y t := by
      funext ω
      simp only [ProbabilityTheory.increment, h0]
      simp
    rwa [heq] at hm2
  obtain ⟨Z, hZmeas, hZae⟩ := hAe
  obtain ⟨U0, hU0⟩ := wiener_atom_sq_le_cesaro_measurable P Z hZmeas x ε hε
  refine ⟨U0, fun U hU => ?_⟩
  have hbound := hU0 U hU
  have hnull : P {ω : Omega | Y t ω ≠ Z ω} = 0 := by
    have h := (MeasureTheory.ae_iff).mp hZae
    exact h
  have hsub1 : {ω : Omega | Y t ω = x} \ {ω : Omega | Z ω = x}
      ⊆ {ω : Omega | Y t ω ≠ Z ω} := by
    intro ω hω
    simp only [Set.mem_diff, Set.mem_setOf_eq] at hω
    simp only [Set.mem_setOf_eq]
    exact fun h => hω.2 (h ▸ hω.1)
  have hsub2 : {ω : Omega | Z ω = x} \ {ω : Omega | Y t ω = x}
      ⊆ {ω : Omega | Y t ω ≠ Z ω} := by
    intro ω hω
    simp only [Set.mem_diff, Set.mem_setOf_eq] at hω
    simp only [Set.mem_setOf_eq]
    exact fun h => hω.2 (h.symm ▸ hω.1)
  have hatom : P {omega : Omega | Y t omega = x} = P {omega : Omega | Z omega = x} :=
    MeasureTheory.measure_congr ((MeasureTheory.ae_eq_set).mpr
      ⟨MeasureTheory.measure_mono_null hsub1 hnull,
       MeasureTheory.measure_mono_null hsub2 hnull⟩)
  have hcos : ∀ u : Real, (∫ omega, Real.cos (u * Y t omega) ∂P)
      = (∫ omega, Real.cos (u * Z omega) ∂P) := by
    intro u
    apply MeasureTheory.integral_congr_ae
    exact hZae.mono fun ω hω => congrArg (fun y => Real.cos (u * y)) hω
  have hsin : ∀ u : Real, (∫ omega, Real.sin (u * Y t omega) ∂P)
      = (∫ omega, Real.sin (u * Z omega) ∂P) := by
    intro u
    apply MeasureTheory.integral_congr_ae
    exact hZae.mono fun ω hω => congrArg (fun y => Real.sin (u * y)) hω
  have hces : (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Y t omega) ∂P)^2 + (∫ omega, Real.sin (u * Y t omega) ∂P)^2) ∂volume)
      = (∫⁻ u in Set.Icc (0 : Real) U, ENNReal.ofReal ((∫ omega, Real.cos (u * Z omega) ∂P)^2 + (∫ omega, Real.sin (u * Z omega) ∂P)^2) ∂volume) := by
    apply MeasureTheory.lintegral_congr
    intro u
    rw [hcos u, hsin u]
  rw [hatom, hces]
  exact hbound
