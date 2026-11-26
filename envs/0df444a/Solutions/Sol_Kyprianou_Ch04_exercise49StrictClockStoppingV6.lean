-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49StrictClockStoppingV6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:38:49.082558+00:00
-- url     : https://prove2.me/submissions/4189ccfc-828b-4291-a067-d6d32ab46c7b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49RationalClockEqV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (X : NNReal → Ω → ℝ)
    (hm : ∀ t, Measurable (X t))
    (hr : ∀ w t, ContinuousWithinAt (fun u => X u w) (Ici t) t)
    (h0 : ∀ w, X 0 w = 0)
    (ha : ∀ t, Measurable[F t] (X t)) :
    IsStoppingTime F.rightCont (fun w => sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0}) := by
  classical
  let τ : Ω → WithTop NNReal := fun w => sInf {v : WithTop NNReal |
    ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0}
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro s
  have he : {w | τ w < (s : WithTop NNReal)} =
      ⋃ q : ℚ, {w | 0 < (q : ℝ) ∧ Real.toNNReal q < s ∧ X (Real.toNNReal q) w < 0} := by
    ext w
    rw [Set.mem_setOf_eq, show τ w = _ from
      Kyprianou.Ch04.exercise49RationalClockEqV3 (fun t => X t w)
        (by rw [h0 w]) (hr w)]
    rw [iInf_lt_iff]
    simp only [Set.mem_iUnion,Set.mem_setOf_eq]
    constructor
    · rintro ⟨q,hq⟩
      by_cases h : 0 < (q : ℝ) ∧ X (Real.toNNReal q) w < 0
      · rw [if_pos h,WithTop.coe_lt_coe] at hq
        exact ⟨q,h.1,hq,h.2⟩
      · rw [if_neg h] at hq
        exact (not_lt_of_ge le_top hq).elim
    · rintro ⟨q,hq,hs,hx⟩
      exact ⟨q,by rw [if_pos ⟨hq,hx⟩,WithTop.coe_lt_coe]; exact hs⟩
  change MeasurableSet[F.rightCont s] {w | τ w < (s : WithTop NNReal)}
  rw [he]
  apply MeasurableSet.iUnion
  intro q
  by_cases h : 0 < (q : ℝ) ∧ Real.toNNReal q < s
  · have hle : Real.toNNReal q ≤ s := h.2.le
    have hM : Measurable[F.rightCont s] (X (Real.toNNReal q)) :=
      (ha _).mono ((F.mono hle).trans (F.le_rightCont s)) le_rfl
    have hS : MeasurableSet[F.rightCont s] (X (Real.toNNReal q) ⁻¹' Iio (0 : ℝ)) :=
      hM measurableSet_Iio
    convert hS using 1
    ext w
    simp [h.1,h.2]
  · have hz : {w : Ω | 0 < (q : ℝ) ∧ Real.toNNReal q < s ∧ X (Real.toNNReal q) w < 0} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      exact fun hw => h ⟨hw.1,hw.2.1⟩
    rw [hz]
    exact @MeasurableSet.empty Ω (F.rightCont s)
