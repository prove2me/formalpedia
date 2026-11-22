-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m81_renewal_conv_support_atomless_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:47:16.531647+00:00
-- url     : https://prove2.me/submissions/23f0be36-38ca-460c-a748-52e79cc377d7

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    (μ (Iio (0:ℝ)) = 0 → ν (Iio (0:ℝ)) = 0 → (μ.conv ν) (Iio (0:ℝ)) = 0) ∧
    ((∀ y : ℝ, ν {y} = 0) → ∀ x : ℝ, (μ.conv ν) {x} = 0) := by
  have h_add : Measurable (fun p : ℝ × ℝ => p.1 + p.2) :=
    measurable_fst.add measurable_snd
  have h_def : μ.conv ν = (μ.prod ν).map (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  constructor
  · intro hμ hν
    rw [h_def, MeasureTheory.Measure.map_apply h_add measurableSet_Iio]
    refine MeasureTheory.measure_mono_null
      (t := (Set.Iio (0:ℝ) ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio (0:ℝ))) ?_
      (MeasureTheory.measure_union_null ?_ ?_)
    · intro p hp
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_union, Set.mem_prod,
        Set.mem_univ, and_true, true_and] at hp ⊢
      by_contra h
      push_neg at h
      linarith [add_nonneg h.1 h.2]
    · simp [MeasureTheory.Measure.prod_prod, hμ]
    · simp [MeasureTheory.Measure.prod_prod, hν]
  · intro ha x
    rw [h_def, MeasureTheory.Measure.map_apply h_add (MeasurableSet.singleton x),
      MeasureTheory.Measure.prod_apply (h_add (MeasurableSet.singleton x))]
    simp [show ∀ a : ℝ, ν
        (Prod.mk a ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' ({x} : Set ℝ))) = 0 from
      fun a => by
        simp only [show (Prod.mk a ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' ({x} : Set ℝ))) =
          {x - a} from by
            ext b
            simp only [Set.mem_preimage, Set.mem_singleton_iff]
            constructor <;> intro h <;> linarith, ha]]
