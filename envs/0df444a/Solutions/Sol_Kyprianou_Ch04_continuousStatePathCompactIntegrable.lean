-- Prove2me | solution 1 for Kyprianou.Ch04.continuousStatePathCompactIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:44:01.661021+00:00
-- url     : https://prove2.me/submissions/28d76300-123e-4dcd-a4d5-421690285c0b

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch03_reflectionSignedCompactBoundV1
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

/-- A continuous time-state function along a measurable cadlag path is locally integrable. -/
theorem solution (Y : NNReal → ℝ) (hY : IsCadlag Y)
    (hm : Measurable (fun r : ℝ => Y r.toNNReal))
    (a : ℝ × ℝ → ℝ) (ha : Continuous a) (t : NNReal) :
    IntegrableOn (fun r => a (r,Y r.toNNReal)) (Icc (0 : ℝ) (t : ℝ)) volume := by
  obtain ⟨A,hA⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1 Y hY 1 t
  obtain ⟨B,hB⟩ := Kyprianou.Ch03.reflectionSignedCompactBoundV1 Y hY (-1) t
  let K := Icc (0 : ℝ) (t : ℝ) ×ˢ Icc (-B) A
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C,hC⟩ := hK.bddAbove_image ha.norm.continuousOn
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) (t : ℝ))) := ⟨by simp [Real.volume_Icc]⟩
  refine (integrable_const C).mono' (ha.measurable.comp (measurable_id.prodMk hm)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hr' : r.toNNReal ∈ Icc (0 : NNReal) t :=
    ⟨zero_le,Real.toNNReal_le_iff_le_coe.mpr hr.2⟩
  have h1 := hA (mem_image_of_mem (fun s => (1:ℝ)*Y s) hr')
  have h2 := hB (mem_image_of_mem (fun s => (-1:ℝ)*Y s) hr')
  simp only [one_mul] at h1
  simp only [neg_mul,one_mul] at h2
  exact hC (mem_image_of_mem (fun p => ‖a p‖) (show (r,Y r.toNNReal) ∈ K from ⟨hr,by constructor <;> linarith⟩))
