-- Prove2me | solution 1 for Kyprianou.Ch03.firstPassageZero_consequence2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:26:59.51301+00:00
-- url     : https://prove2.me/submissions/fbfbc59d-231e-4fb8-a027-a3dc9c592328

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch03_firstPassageZero_consequence1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hNotDecreasing : ¬ (∀ᵐ omega : Omega ∂ P,
      Antitone (fun t : NNReal => L.X t omega))) :
        forall phi : Real,
      (0 <= phi ∧ L.ψ phi = 0 ∧ (forall theta : Real, 0 <= theta ->
        L.ψ theta = 0 -> theta <= phi)) ->
      (forall x : Real, 0 < x ->
        ((P {omega : Omega |
          firstHittingTime L.X (Set.Ioi x) omega != ⊤}).toReal = 1
          <-> phi = 0)) := by
  refine fun phi hRoot x hx => ?_
  classical
  have hTime (omega : Omega) :
      ∃ t : NNReal,
        firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
          firstHittingTime L.X (Set.Ioi x) omega =
            (t : WithTop NNReal) := by
    by_cases h : firstHittingTime L.X (Set.Ioi x) omega = ⊤
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h
      refine ⟨t, fun _ => ?_⟩
      first | exact ht | exact ht.symm
  let f : Omega → NNReal := fun omega => Classical.choose (hTime omega)
  have hf (omega : Omega) :
      firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤ →
        firstHittingTime L.X (Set.Ioi x) omega =
          (f omega : WithTop NNReal) :=
    Classical.choose_spec (hTime omega)
  have hfBool (omega : Omega)
      (h : firstHittingTime L.X (Set.Ioi x) omega != ⊤) :
      firstHittingTime L.X (Set.Ioi x) omega =
        (f omega : WithTop NNReal) := by
    by_cases hne : firstHittingTime L.X (Set.Ioi x) omega ≠ ⊤
    · exact hf omega hne
    · have heq : firstHittingTime L.X (Set.Ioi x) omega = ⊤ := by
        by_contra hnot
        exact hne hnot
      simp [heq] at h
  have htail :=
    Kyprianou.Ch03.firstPassageZero_consequence1
      P F L hNotDecreasing phi hRoot x (le_of_lt hx) f hfBool
  rw [htail]
  constructor
  · refine fun heq => ?_
    have hmul : phi * x = 0 := by
      have h := (Real.exp_eq_one_iff ((-phi) * x)).mp heq
      nlinarith
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact False.elim ((ne_of_gt hx) h)
  · refine fun h => ?_
    rw [h]
    norm_num

