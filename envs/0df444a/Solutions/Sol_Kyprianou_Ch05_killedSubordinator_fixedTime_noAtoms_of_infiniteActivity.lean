-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_fixedTime_noAtoms_of_infiniteActivity
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:57:25.980174+00:00
-- url     : https://prove2.me/submissions/93c60806-8a3f-4660-affa-5f461a6ee7ca

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_atom_sq_le_cesaro_chf
import Theorems.Thm_Kyprianou_Ch05_killedSubordinator_cesaro_chf_tendsto_zero
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
    ∀ t : NNReal, 0 < t → ∀ x : Real,
      P {omega : Omega | Y t omega = x} = 0) := by
  intro hPi t ht x
  have key : ∀ ε : ℝ≥0∞, 0 < ε →
      (P {omega : Omega | Y t omega = x}) ^ 2 ≤ ε + ε := by
    intro ε hε
    obtain ⟨W0, hW0⟩ := Kyprianou.Ch05.killedSubordinator_cesaro_chf_tendsto_zero
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential hPi t ht ε hε
    obtain ⟨W0', hW0'⟩ := Kyprianou.Ch05.killedSubordinator_atom_sq_le_cesaro_chf
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential t ht x ε hε
    exact (hW0' (max W0 W0') (le_max_right _ _)).trans
      (add_le_add_left (hW0 (max W0 W0') (le_max_left _ _)) _)
  by_contra hne
  have hp1 : P {omega : Omega | Y t omega = x} ≤ 1 := by
    rw [← measure_univ (μ := P)]
    exact measure_mono (Set.subset_univ _)
  set a : ℝ≥0∞ := (P {omega : Omega | Y t omega = x}) ^ 2 with ha
  have hptop : P {omega : Omega | Y t omega = x} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top hp1
  have hpfin : a ≠ ⊤ := ENNReal.pow_ne_top hptop
  have hp2pos : 0 < a := lt_of_le_of_ne zero_le (Ne.symm (pow_ne_zero 2 hne))
  have hε : (0 : ℝ≥0∞) < a / 2 / 2 :=
    ENNReal.div_pos (ENNReal.div_pos hp2pos.ne' (by norm_num)).ne' (by norm_num)
  have h1 := key _ hε
  have h2 : a / 2 / 2 + a / 2 / 2 = a / 2 := ENNReal.add_halves _
  have h3 : a / 2 < a := ENNReal.half_lt_self (pow_ne_zero 2 hne) hpfin
  exact absurd (h1.trans_eq h2) (not_le.mpr h3)
