-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46NonzeroStrictPassageNotAntitoneV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:48:35.493793+00:00
-- url     : https://prove2.me/submissions/2a5203af-1d7c-43de-b0ac-d9540d51e845

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A nonzero positive-level killed transform rules out antitone paths. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (beta : Real)
    (hNonzero : (∫ w,
      if Kyprianou.Ch03.firstHittingTime L.X (Ioi (1 : Real)) w = ⊤
      then (0 : Real) else Real.exp (-beta *
        (((Kyprianou.Ch03.firstHittingTime L.X (Ioi (1 : Real)) w).untopD 0 : NNReal) : Real))
      ∂P) ≠ 0) :
    ¬ (∀ᵐ w ∂P, Antitone (fun t : NNReal => L.X t w)) := by
  intro ha
  apply hNonzero
  apply integral_eq_zero_of_ae
  filter_upwards [ha] with w hw
  have hs : {t : NNReal | 0 < t ∧ L.X t w ∈ Ioi (1 : Real)} = ∅ := by
    ext t
    simp only [mem_setOf_eq, mem_Ioi, mem_empty_iff_false, iff_false]
    intro ht
    have hle := hw (zero_le : (0 : NNReal) ≤ t)
    change L.X t w ≤ L.X 0 w at hle
    rw [L.X_zero] at hle
    linarith [ht.2]
  have ht : Kyprianou.Ch03.firstHittingTime L.X (Ioi (1 : Real)) w = ⊤ := by
    unfold Kyprianou.Ch03.firstHittingTime
    rw [hs, image_empty, sInf_empty]
  simp [ht]
