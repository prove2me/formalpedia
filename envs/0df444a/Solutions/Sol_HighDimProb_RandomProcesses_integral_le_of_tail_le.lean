-- Prove2me | solution 1 for HighDimProb.RandomProcesses.integral_le_of_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:49:58.430987+00:00
-- url     : https://prove2.me/submissions/fef3dc78-a14e-40cd-a269-77718748c518

import Mathlib

open MeasureTheory ProbabilityTheory Set

namespace SlepianProof

lemma integral_nonneg_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hYnonneg : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ t, 0 < t → P.real {ω | t ≤ X ω} ≤ P.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all P hXnonneg) hX.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all P hYnonneg) hY.aestronglyMeasurable]
  apply ENNReal.toReal_mono hY.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_le P (ae_of_all P hXnonneg) hX.aemeasurable,
    lintegral_eq_lintegral_meas_le P (ae_of_all P hYnonneg) hY.aemeasurable]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
    (htail t ht)

lemma integral_nonneg_le_of_strict_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hYnonneg : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ t, 0 < t → P.real {ω | t < X ω} ≤ P.real {ω | t < Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all P hXnonneg) hX.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all P hYnonneg) hY.aestronglyMeasurable]
  apply ENNReal.toReal_mono hY.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_lt P (ae_of_all P hXnonneg) hX.aemeasurable,
    lintegral_eq_lintegral_meas_lt P (ae_of_all P hYnonneg) hY.aemeasurable]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
    (htail t ht)

lemma integral_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (htail : ∀ t : ℝ, P.real {ω | t ≤ X ω} ≤ P.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  have hXp : Integrable (fun ω => max (X ω) 0) P := hX.sup (integrable_const 0)
  have hYp : Integrable (fun ω => max (Y ω) 0) P := hY.sup (integrable_const 0)
  have hXn : Integrable (fun ω => max (-X ω) 0) P := hX.neg.sup (integrable_const 0)
  have hYn : Integrable (fun ω => max (-Y ω) 0) P := hY.neg.sup (integrable_const 0)
  have hpos : (∫ ω, max (X ω) 0 ∂P) ≤ ∫ ω, max (Y ω) 0 ∂P := by
    apply integral_nonneg_le_of_tail_le P _ _ hXp hYp
      (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)
    intro t ht
    simpa only [le_max_iff, not_le.mpr ht, or_false] using htail t
  have hneg : (∫ ω, max (-Y ω) 0 ∂P) ≤ ∫ ω, max (-X ω) 0 ∂P := by
    apply integral_nonneg_le_of_strict_tail_le P _ _ hYn hXn
      (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)
    intro t ht
    have hx : P.real {ω | X ω < -t} = 1 - P.real {ω | -t ≤ X ω} := by
      convert probReal_compl_eq_one_sub₀
        (nullMeasurableSet_le aemeasurable_const hX.aemeasurable) using 1
      congr 1
      ext ω
      simp
    have hy : P.real {ω | Y ω < -t} = 1 - P.real {ω | -t ≤ Y ω} := by
      convert probReal_compl_eq_one_sub₀
        (nullMeasurableSet_le aemeasurable_const hY.aemeasurable) using 1
      congr 1
      ext ω
      simp
    have hsets (Z : Ω → ℝ) : {ω | t < max (-Z ω) 0} = {ω | Z ω < -t} := by
      ext ω
      simp only [mem_setOf_eq, lt_max_iff, not_lt.mpr ht.le, or_false]
      constructor <;> intro h <;> linarith
    rw [hsets Y, hsets X, hx, hy]
    linarith [htail (-t)]
  have hx : (∫ ω, X ω ∂P) = (∫ ω, max (X ω) 0 ∂P) - ∫ ω, max (-X ω) 0 ∂P := by
    rw [← integral_sub hXp hXn]
    congr 1
    funext ω
    exact (max_zero_sub_eq_self (X ω)).symm
  have hy : (∫ ω, Y ω ∂P) = (∫ ω, max (Y ω) 0 ∂P) - ∫ ω, max (-Y ω) 0 ∂P := by
    rw [← integral_sub hYp hYn]
    congr 1
    funext ω
    exact (max_zero_sub_eq_self (Y ω)).symm
  rw [hx, hy]
  linarith

end SlepianProof

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (htail : ∀ t : ℝ, P.real {ω | t ≤ X ω} ≤ P.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  exact SlepianProof.integral_le_of_tail_le P X Y hX hY htail
