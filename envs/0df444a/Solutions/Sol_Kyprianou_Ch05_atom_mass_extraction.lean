-- Prove2me | solution 1 for Kyprianou.Ch05.atom_mass_extraction
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T12:12:40.956634+00:00
-- url     : https://prove2.me/submissions/e61f0cfc-8e25-48c3-a189-0f92e7b8ae50

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
  (Pi (Set.Ioi (0 : Real)) = ⊤ →
    ∀ δ : Real, 0 < δ → δ ≤ 1 → ∀ c : Real,
      c * (Pi (Set.Icc δ 1)).toReal < (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal →
      ∃ y ∈ Set.Icc δ 1, c ≤ (Pi {y}).toReal) := by
  intro _hPi δ hδ hδ1 c hlt
  have hLevy : (∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi) < ⊤ :=
    hTriplet.2.2.2.1
  -- Pi (Icc δ 1) is finite for 0 < δ ≤ 1, via the Lévy integrability field
  have hfin : Pi (Set.Icc δ 1) < ⊤ := by
    have hstep : ENNReal.ofReal δ * Pi (Set.Icc δ 1)
        ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi := by
      calc ENNReal.ofReal δ * Pi (Set.Icc δ 1)
          = ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal δ ∂Pi := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
              (Eventually.of_forall (fun y hy => ENNReal.ofReal_le_ofReal (le_min hδ1 hy.1))))
        _ ≤ ∫⁻ y in Set.Ioi (0 : Real), ENNReal.ofReal (min 1 y) ∂Pi :=
            lintegral_mono_set (fun y hy => lt_of_lt_of_le hδ hy.1)
    by_contra htop
    have htop' : Pi (Set.Icc δ 1) = ⊤ := top_unique (not_lt.mp htop)
    rw [htop', ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))] at hstep
    exact lt_irrefl _ (lt_of_le_of_lt hstep hLevy)
  -- contrapositive: if every atom mass in Icc δ 1 is < c, the integral bound fails
  by_contra hcon
  push_neg at hcon
  have hcpos : 0 < c := lt_of_le_of_lt ENNReal.toReal_nonneg (hcon δ ⟨le_rfl, hδ1⟩)
  have hpt : ∀ y ∈ Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ≤ ENNReal.ofReal c :=
    fun y hy => ENNReal.ofReal_le_ofReal (hcon y hy).le
  have hbound : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi)
      ≤ ENNReal.ofReal c * Pi (Set.Icc δ 1) := by
    calc (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi)
        ≤ ∫⁻ y in Set.Icc δ 1, ENNReal.ofReal c ∂Pi :=
          lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
            (Eventually.of_forall (fun y hy => hpt y hy)))
      _ = ENNReal.ofReal c * Pi (Set.Icc δ 1) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
  have hprod_ne : ENNReal.ofReal c * Pi (Set.Icc δ 1) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hint_ne : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi) ≠ ⊤ :=
    ne_top_of_le_ne_top hprod_ne hbound
  have hle : (∫⁻ y in Set.Icc δ 1, ENNReal.ofReal ((Pi {y}).toReal) ∂Pi).toReal
      ≤ c * (Pi (Set.Icc δ 1)).toReal := by
    have h := (ENNReal.toReal_le_toReal hint_ne hprod_ne).mpr hbound
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le] at h
  exact (not_lt.mpr hle) hlt
