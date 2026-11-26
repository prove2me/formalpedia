-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46PredictablePrelevelEventV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:21:42.944721+00:00
-- url     : https://prove2.me/submissions/fb0106a3-792d-44fc-86a1-b0bb25827f56

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46CappedArrivalPredictableV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictableBeforeClockV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictableTimeCapV1
import Theorems.Thm_Kyprianou_Ch04_predictableLeftVersionV1
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (T : NNReal) :
    MeasurableSet[G.rightCont.predictable] {p : NNReal × Omega |
      A p.2 < (p.1 : WithTop NNReal) ∧ p.1 ≤ T ∧
      Function.leftLim (fun u : NNReal => L.X u p.2) p.1 =
        (((A p.2).untopD 0 : NNReal) : Real)} := by
  have hAdapt : StronglyAdapted G.rightCont L.X := by
    intro t
    exact ((L.adapted t).mono (G.le_rightCont t) le_rfl).stronglyMeasurable
  have hLeft := Kyprianou.Ch04.predictableLeftVersionV1 G.rightCont L.X hAdapt
    (fun w t _ => ⟨_,(avram_p2_a_zero_rate_original_cadlag_regular_all_times L w).1 t⟩)
  have hH := Kyprianou.Ch04.exercise46CappedArrivalPredictableV1 G A hA
  have hmL : Measurable[G.rightCont.predictable] (fun p : NNReal × Omega =>
      Function.leftLim (fun u : NNReal => L.X u p.2) p.1) := hLeft.measurable
  have hmH : Measurable[G.rightCont.predictable] (fun p : NNReal × Omega =>
      (((min (A p.2) (p.1 : WithTop NNReal)).untopD 0 : NNReal) : Real)) := hH.measurable
  have hAfter : MeasurableSet[G.rightCont.predictable] {p : NNReal × Omega |
      A p.2 < (p.1 : WithTop NNReal)} := by
    simpa only [compl_setOf, not_le] using
      (Kyprianou.Ch04.exercise46PredictableBeforeClockV1 G.rightCont A hA).compl
  have hCap := Kyprianou.Ch04.exercise46PredictableTimeCapV1 G.rightCont T
  have hEq := @measurableSet_eq_fun _ _ G.rightCont.predictable _ _ _ _ hmL hmH
  have he : {p : NNReal × Omega | A p.2 < (p.1 : WithTop NNReal) ∧ p.1 ≤ T ∧
      Function.leftLim (fun u : NNReal => L.X u p.2) p.1 =
        (((A p.2).untopD 0 : NNReal) : Real)} =
      {p | A p.2 < (p.1 : WithTop NNReal)} ∩
        ({p | p.1 ≤ T} ∩ {p | Function.leftLim (fun u : NNReal => L.X u p.2) p.1 =
          (((min (A p.2) (p.1 : WithTop NNReal)).untopD 0 : NNReal) : Real)}) := by
    ext p
    simp only [mem_setOf_eq,mem_inter_iff]
    constructor
    · rintro ⟨ha,hcap,heq⟩
      exact ⟨ha,hcap,by rw [min_eq_left ha.le]; exact heq⟩
    · rintro ⟨ha,hcap,heq⟩
      rw [min_eq_left ha.le] at heq
      exact ⟨ha,hcap,heq⟩
  rw [he]
  exact hAfter.inter (hCap.inter hEq)
