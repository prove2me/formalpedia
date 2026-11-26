-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46FirstMarkTruncatedCompensationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:40:41.528918+00:00
-- url     : https://prove2.me/submissions/a72b2bb7-e317-4dd7-9918-feca7a571a48

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46ClockMaskPredictableV1
import Theorems.Thm_Kyprianou_Ch04_exercise46PredictableMarkedCountMeanV1
import Theorems.Thm_Kyprianou_Ch04_exercise46FirstMarkedCountPathV1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G)
    (A : Omega → WithTop NNReal) (hA : IsStoppingTime G.rightCont A)
    (hAm : Measurable A)
    (hFirst : ∀ᵐ w ∂P, A w = ((A w).untopD 0 : NNReal) ∧
      0 < (A w).untopD 0 ∧
      L.X ((A w).untopD 0) w <
        Function.leftLim (fun u : NNReal => L.X u w) ((A w).untopD 0) ∧
      ∀ u : NNReal, 0 < u → u < (A w).untopD 0 →
        L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (T : NNReal) (B : Set Real) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : Real)) :
    let a : Omega → NNReal := fun w => (A w).untopD 0
    let J : Omega → Real := fun w =>
      L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w)
    let E : Set (NNReal × Omega) :=
      {p | 0 < p.1 ∧ p.1 ≤ T ∧ (p.1 : WithTop NNReal) ≤ A p.2}
    P {w | A w ≤ (T : WithTop NNReal) ∧ J w ∈ B} =
      ((((volume : Measure Real).restrict (Icc 0 (T : Real))).map Real.toNNReal).prod P) E *
        L.ν B := by
  classical
  dsimp only
  let a : Omega → NNReal := fun w => (A w).untopD 0
  let J : Omega → Real := fun w =>
    L.X (a w) w - Function.leftLim (fun u : NNReal => L.X u w) (a w)
  let E : Set (NNReal × Omega) :=
    {p | 0 < p.1 ∧ p.1 ≤ T ∧ (p.1 : WithTop NNReal) ≤ A p.2}
  let NX : Omega → Measure (NNReal × Real) := fun w =>
    ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
      Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
      (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
  have hE : MeasurableSet[G.rightCont.predictable] E :=
    Kyprianou.Ch04.exercise46ClockMaskPredictableV1 G A hA T
  have hC := Kyprianou.Ch04.exercise46PredictableMarkedCountMeanV1
    P G L T E hE (fun p hp => hp.2.1) B hB hNeg
  have hJ : Measurable J :=
    (avram_wave4_04a_actual_levy_jumpmark_joint_measurable L).comp
      (((WithTop.measurable_untopD (0 : NNReal)).comp hAm).prodMk measurable_id)
  let D : Set Omega := {w | A w ≤ (T : WithTop NNReal) ∧ J w ∈ B}
  have hD : MeasurableSet D :=
    (measurableSet_le hAm measurable_const).inter (hJ hB)
  have he : (fun w => NX w {p | (p.1,w) ∈ E ∧ p.2 ∈ B}) =ᵐ[P]
      D.indicator (fun _ => (1 : ENNReal)) := by
    filter_upwards [hFirst] with w hw
    have hset : {p : NNReal × Real | (p.1,w) ∈ E ∧ p.2 ∈ B} =
        Ioc 0 (min (a w) T) ×ˢ B := by
      ext p
      change (0 < p.1 ∧ p.1 ≤ T ∧ (p.1 : WithTop NNReal) ≤ A w) ∧
        p.2 ∈ B ↔ p ∈ Ioc 0 (min (a w) T) ×ˢ B
      rw [hw.1]
      simp only [mem_prod, mem_Ioc, le_min_iff, WithTop.coe_le_coe]
      tauto
    rw [hset]
    have hjump : L.X (a w) w -
        Function.leftLim (fun u : NNReal => L.X u w) (a w) ≠ 0 :=
      sub_ne_zero.mpr (ne_of_lt hw.2.2.1)
    have hc := Kyprianou.Ch04.exercise46FirstMarkedCountPathV1
      P G L w (a w) T hw.2.1 hjump hw.2.2.2 B hB
    change NX w (Ioc 0 (min (a w) T) ×ˢ B) = _
    rw [hc]
    have htime : A w ≤ (T : WithTop NNReal) ↔ a w ≤ T := by
      rw [hw.1]
      exact WithTop.coe_le_coe
    rw [indicator_apply]
    have hmem : w ∈ D ↔ a w ≤ T ∧ J w ∈ B := by
      change (A w ≤ (T : WithTop NNReal) ∧ J w ∈ B) ↔ _
      exact and_congr_left' htime
    by_cases h : a w ≤ T ∧ J w ∈ B
    · rw [if_pos h, if_pos (hmem.mpr h)]
    · rw [if_neg h, if_neg (fun hd => h (hmem.mp hd))]
  change P D = _
  rw [← hC, lintegral_congr_ae he]
  change P D = ∫⁻ w, D.indicator (1 : Omega → ENNReal) w ∂P
  exact (lintegral_indicator_one hD).symm
