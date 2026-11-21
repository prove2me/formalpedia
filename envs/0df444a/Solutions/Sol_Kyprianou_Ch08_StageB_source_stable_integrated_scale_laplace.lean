-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_stable_integrated_scale_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:47:47.823354+00:00
-- url     : https://prove2.me/submissions/11818750-190b-417c-ba43-c8a9c89a82af

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_Phi_below_beta
import Theorems.Thm_Kyprianou_Ch08_StageB_source_stable_ratio_lt_one
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
set_option autoImplicit false
open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (α q β : ℝ) (W : ℝ → ℝ → ℝ)
    (hα : 1 < α) (hq : 0 < q) (hβ : q ^ (1 / α) < β)
    (hW : HasSourceScaleFamily (fun v : ℝ => v ^ α) W) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) *
      integratedScale (W q) x ∂volume) =
      (β * (β ^ α - q))⁻¹ := by
  have hqroot : 0 ≤ q ^ (1 / α) := Real.rpow_nonneg hq.le _
  have hβ0 : 0 < β := lt_of_le_of_lt hqroot hβ
  have hΦ := source_stable_Phi_below_beta α q β hα hq hβ
    (hW q hq.le).1
  have hsource := ((hW q hq.le).2.2.2.2.2 β hβ0.le hΦ)
  have hbase : IntegrableOn (fun x : ℝ =>
      Real.exp (-(β * x)) * W q x) (Set.Ioi (0 : ℝ)) volume := by
    simpa only [neg_mul] using hsource.1
  have hprim := AvramDividend.Classical.positive_laplace_interval_primitive_real
    (W q) β hβ0 hbase
  have hgap : q < β ^ α := (div_lt_one (Real.rpow_pos_of_pos hβ0 _)).mp
    (source_stable_ratio_lt_one α q β hα hq hβ).2
  have hs : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) * W q x ∂volume) =
      (β ^ α - q)⁻¹ := by
    simpa only [neg_mul] using hsource.2
  have hresult : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      integratedScale (W q) x ∂volume) =
      (β ^ α - q)⁻¹ / β := by
    simpa only [integratedScale] using
      hprim.2.trans (congrArg (fun z : ℝ => z / β) hs)
  have hh : (∫ x in Set.Ioi (0 : ℝ), Real.exp (-(β * x)) *
      integratedScale (W q) x ∂volume) =
      (β * (β ^ α - q))⁻¹ := by
    rw [hresult]
    field_simp [ne_of_gt hβ0, ne_of_gt (sub_pos.mpr hgap)]
  simpa only [neg_mul] using hh
