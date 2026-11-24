-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_factor_positive_time_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:44:07.300029+00:00
-- url     : https://prove2.me/submissions/be5f6453-9637-426b-bac6-4b44d2dd9644

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (U : Ω → ℝ≥0) (hU : Measurable U)
    (F : ℝ≥0 → Ω → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    (∫⁻ ω, ∫⁻ s : ℝ≥0, F (U ω + s) ω ∂positiveTimeLebesgue ∂P) =
      ∫⁻ ω, ∫⁻ t : ℝ≥0, if U ω ≤ t then F t ω else 0 ∂positiveTimeLebesgue ∂P := by
  apply lintegral_congr
  intro ω
  let u := U ω
  let f : ℝ≥0 → ℝ≥0∞ := fun t => F t ω
  have hf : Measurable f := hF.comp (measurable_id.prodMk measurable_const)
  have hg : Measurable (fun t : ℝ≥0 => f (u + t)) :=
    hf.comp (measurable_const.add measurable_id)
  have hh : Measurable (fun t : ℝ≥0 => if u ≤ t then f t else 0) :=
    Measurable.ite (measurableSet_le measurable_const measurable_id) hf measurable_const
  change (∫⁻ s, f (u + s) ∂positiveTimeLebesgue) =
    ∫⁻ t, (if u ≤ t then f t else 0) ∂positiveTimeLebesgue
  unfold positiveTimeLebesgue
  rw [lintegral_map hg measurable_real_toNNReal, lintegral_map hh measurable_real_toNNReal]
  let g : ℝ → ℝ≥0∞ := fun t => f t.toNNReal
  have hpre : (fun s : ℝ => s + (u : ℝ)) ⁻¹' Ici (u : ℝ) = Ici 0 := by
    ext s
    simp
  have hMP := measurePreserving_add_right (volume : Measure ℝ) (u : ℝ)
  have hmp := hMP.setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight (u : ℝ)) g (Ici (u : ℝ))
  rw [hpre] at hmp
  calc
    _ = ∫⁻ s in Ici (0 : ℝ), g (s + (u : ℝ)) := by
      apply setLIntegral_congr_fun measurableSet_Ici
      intro s hs
      have hs0 : 0 ≤ s := hs
      have he : (s + (u : ℝ)).toNNReal = u + s.toNNReal := by
        apply NNReal.eq
        rw [Real.coe_toNNReal _ (add_nonneg hs0 u.coe_nonneg), NNReal.coe_add,
          Real.coe_toNNReal _ hs0]
        ring
      simp only [g, he]
    _ = ∫⁻ t in Ici (u : ℝ), g t := hmp
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ici]
      apply lintegral_congr
      intro t
      by_cases ht : 0 ≤ t
      · have hiff : u ≤ t.toNNReal ↔ (u : ℝ) ≤ t := by
          rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht]
        simp [Set.indicator_apply, g, ht, hiff]
      · have hn : ¬ (u : ℝ) ≤ t := fun h => ht (u.coe_nonneg.trans h)
        simp [Set.indicator_apply, ht, hn]
