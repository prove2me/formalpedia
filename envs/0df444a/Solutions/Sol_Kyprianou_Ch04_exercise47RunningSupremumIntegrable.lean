-- Prove2me | solution 1 for Kyprianou.Ch04.exercise47RunningSupremumIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:03:02.585439+00:00
-- url     : https://prove2.me/submissions/77630950-32f8-4fce-abc3-a00025da5c9e

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable

open MeasureTheory AvramDividend.Classical Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F) :
    forall t : NNReal,
      Integrable
        (fun omega : Omega =>
          sSup ((fun s : NNReal => L.X s omega) '' Set.Iic t)) P := by
  intro t
  haveI : IsProbabilityMeasure P := L.isProbability
  have heq (w : Omega) :
      runningSup L t w = sSup ((fun s : NNReal => L.X s w) '' Set.Iic t) := by
    rw [(runningSup_eq_rawSup_nonneg L t w).1]
    change sSup (Set.range (fun s : Set.Icc (0 : NNReal) t => L.X s.1 w)) = _
    have hset : Set.range (fun s : Set.Icc (0 : NNReal) t => L.X s.1 w) =
        (fun s : NNReal => L.X s w) '' Set.Iic t := by
      ext z
      simp only [Set.mem_range, Set.mem_image, Subtype.exists, Set.mem_Icc,
        Set.mem_Iic, zero_le, true_and, exists_prop]
    rw [hset]
  simp_rw [← heq]
  by_cases hb : L.BoundedVariation
  · have hm : Measurable (runningSup L t) :=
      (levy_runningSup_joint_time_path_measurable L).comp
        (measurable_const.prodMk measurable_id)
    let C : ℝ := (t : ℝ) * max L.drift 0
    have hC : 0 ≤ C := mul_nonneg (NNReal.coe_nonneg _) (le_max_right _ _)
    apply (integrable_const C).mono hm.aestronglyMeasurable
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times L hb] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (runningSup_eq_rawSup_nonneg L t w).2,
      Real.norm_eq_abs, abs_of_nonneg hC, heq]
    apply csSup_le
    · exact ⟨L.X 0 w, ⟨0, Set.mem_Iic.mpr ((show (0 : NNReal) ≤ t from zero_le)), rfl⟩⟩
    · rintro z ⟨s, hs, rfl⟩
      have h := hw (show (0 : NNReal) ≤ s from zero_le)
      simp only [NNReal.coe_zero, zero_mul, L.X_zero, sub_zero] at h
      calc
        _ ≤ (s : ℝ) * L.drift := by linarith
        _ ≤ C := by
          dsimp [C]
          exact (mul_le_mul_of_nonneg_left (le_max_left _ _) (NNReal.coe_nonneg s)).trans
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (le_max_right _ _))
  · exact avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1 L hb t
