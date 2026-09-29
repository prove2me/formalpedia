-- Prove2me | solution 1 for MetricGeometry.comparisonAngle_le_add_of_forall_comparisonAngle_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T00:57:56.94654+00:00
-- url     : https://prove2.me/submissions/9d510da1-3e8f-476a-ab3c-d43a768737b9

import Definitions.Def_metric_geodesic_angle
import Theorems.Thm_MetricGeometry_comparisonAngle_mem_Icc
import Theorems.Thm_MetricGeometry_comparisonAngle_eq_angle
import Theorems.Thm_MetricGeometry_dist_lt_dist_of_comparisonAngle_lt
import Theorems.Thm_InnerProductGeometry_exists_pair_norm_eq_angle_eq
import Theorems.Thm_InnerProductGeometry_exists_mem_segment_angle_eq

open MetricGeometry InnerProductGeometry

theorem solution {X : Type*} [PseudoMetricSpace X]
    (p b e : X) (c : ℝ → X) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : 0 < dist p b) (he : 0 < dist p e)
    (hc : ∀ t ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)), dist p (c t) = t)
    (h1 : ∀ t ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)),
      comparisonAngle p (c t) b ≤ A)
    (h2 : ∀ t ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)),
      comparisonAngle p (c t) e ≤ B) :
    comparisonAngle p b e ≤ A + B := by
  by_contra hcon
  push_neg at hcon
  have hΘpi : comparisonAngle p b e ≤ Real.pi :=
    (MetricGeometry.comparisonAngle_mem_Icc p b e).2
  obtain ⟨α, hα1, hα2⟩ : ∃ α : ℝ, A + B < α ∧ α < comparisonAngle p b e :=
    ⟨(A + B + comparisonAngle p b e) / 2, by linarith, by linarith⟩
  have hα0 : 0 ≤ α := by linarith
  have hαpi : α ≤ Real.pi := by linarith
  obtain ⟨bb, cc, hbn, hcn, hang⟩ :=
    InnerProductGeometry.exists_pair_norm_eq_angle_eq (dist p b) (dist p e) α hb he hα0 hαpi
  have hd0b : dist (0 : ℂ) bb = dist p b := by rw [dist_zero_left, hbn]
  have hd0c : dist (0 : ℂ) cc = dist p e := by rw [dist_zero_left, hcn]
  have hcab : comparisonAngle (0 : ℂ) bb cc = α := by
    rw [MetricGeometry.comparisonAngle_eq_angle, sub_zero, sub_zero, hang]
  have step1 : dist bb cc < dist b e :=
    MetricGeometry.dist_lt_dist_of_comparisonAngle_lt (0 : ℂ) bb cc p b e hb he hd0b hd0c
      (by rw [hcab]; exact hα2)
  have hbb0 : bb ≠ 0 := norm_pos_iff.mp (by rw [hbn]; exact hb)
  have hcc0 : cc ≠ 0 := norm_pos_iff.mp (by rw [hcn]; exact he)
  have hangpi : angle bb cc ≠ Real.pi := by rw [hang]; intro h; linarith
  obtain ⟨α', hα'1, hα'2⟩ : ∃ α' : ℝ, A < α' ∧ α' < α - B :=
    ⟨(A + (α - B)) / 2, by linarith, by linarith⟩
  have hα'0 : 0 ≤ α' := by linarith
  have hα'le : α' ≤ angle bb cc := by rw [hang]; linarith
  obtain ⟨x, hxseg, hx0, hxa1, hxa2, hxnorm⟩ :=
    InnerProductGeometry.exists_mem_segment_angle_eq bb cc hbb0 hcc0 hangpi α' hα'0 hα'le
  have ht0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have htle : ‖x‖ ≤ max (dist p b) (dist p e) := by
    rw [← hbn, ← hcn]; exact hxnorm
  have htmem : ‖x‖ ∈ Set.Ioc (0:ℝ) (max (dist p b) (dist p e)) := ⟨ht0, htle⟩
  have hdct : dist p (c ‖x‖) = ‖x‖ := hc ‖x‖ htmem
  have hd0x : dist (0 : ℂ) x = ‖x‖ := by rw [dist_zero_left]
  have hcax : comparisonAngle (0 : ℂ) x bb = α' := by
    rw [MetricGeometry.comparisonAngle_eq_angle, sub_zero, sub_zero,
      InnerProductGeometry.angle_comm, hxa1]
  have step3 : dist (c ‖x‖) b < dist x bb :=
    MetricGeometry.dist_lt_dist_of_comparisonAngle_lt p (c ‖x‖) b (0 : ℂ) x bb
      (by rw [hd0x]; exact ht0) (by rw [hd0b]; exact hb)
      (by rw [hdct, hd0x]) (by rw [hd0b])
      (by rw [hcax]; exact lt_of_le_of_lt (h1 ‖x‖ htmem) hα'1)
  have hcaxc : comparisonAngle (0 : ℂ) x cc = α - α' := by
    rw [MetricGeometry.comparisonAngle_eq_angle, sub_zero, sub_zero, hxa2, hang]
  have step4 : dist (c ‖x‖) e < dist x cc :=
    MetricGeometry.dist_lt_dist_of_comparisonAngle_lt p (c ‖x‖) e (0 : ℂ) x cc
      (by rw [hd0x]; exact ht0) (by rw [hd0c]; exact he)
      (by rw [hdct, hd0x]) (by rw [hd0c])
      (by rw [hcaxc]; exact lt_of_le_of_lt (h2 ‖x‖ htmem) (by linarith))
  have step5 : dist bb x + dist x cc = dist bb cc := dist_add_dist_of_mem_segment hxseg
  have tri : dist b e ≤ dist b (c ‖x‖) + dist (c ‖x‖) e := dist_triangle _ _ _
  rw [dist_comm b (c ‖x‖)] at tri
  have hxb : dist x bb = dist bb x := dist_comm _ _
  linarith
