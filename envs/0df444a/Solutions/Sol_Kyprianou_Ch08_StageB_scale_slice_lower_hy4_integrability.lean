-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.scale_slice_lower_hy4_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:01:10.44864+00:00
-- url     : https://prove2.me/submissions/f343735b-4011-4652-8957-49433929c647

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
private theorem dm (q : ℝ) : Measurable (fun t : ℝ≥0∞ => discountedAt q t) := by
  have heq : (fun t : ℝ≥0∞ => discountedAt q t) =
      fun t => if t = ⊤ then 0 else Real.exp (-q * t.toReal) := by
    funext t ; induction t using WithTop.recTopCoe with
    | top => exact (if_pos rfl).symm
    | coe s => simp [discountedAt]
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (⊤ : ℝ≥0∞)) measurable_const
    (Real.continuous_exp.measurable.comp (measurable_const.mul ENNReal.measurable_toReal))
private theorem dn (q : ℝ) (hq : 0 ≤ q) (t : WithTop ℝ≥0) : ‖discountedAt q t‖ ≤ 1 := by
  induction t using WithTop.recTopCoe with
  | top => simp [discountedAt]
  | coe s =>
    change ‖Real.exp (-q * (s : ℝ))‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) s.coe_nonneg
theorem solution {Ω : Type*} [m : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (U V : Ω → ℝ≥0∞) (hU : AEMeasurable U μ) (hV : AEMeasurable V μ)
    (q : ℝ) (hq : 0 ≤ q) :
    Integrable (fun ω => discountedAt q (U ω)) μ ∧
      Integrable (fun ω => if U ω < V ω then discountedAt q (U ω) else 0) μ := by
  have hdi : Integrable (fun ω => discountedAt q (U ω)) μ :=
    Integrable.of_bound (((dm q).comp_aemeasurable hU).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => dn q hq _)
  have hpm : Measurable (fun p : ℝ≥0∞ × ℝ≥0∞ =>
      if p.1 < p.2 then discountedAt q p.1 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((dm q).comp measurable_fst) measurable_const
  have hpi : Integrable (fun ω => if U ω < V ω then discountedAt q (U ω) else 0) μ :=
    Integrable.of_bound (by
      change AEStronglyMeasurable
        (((fun p : ℝ≥0∞ × ℝ≥0∞ =>
          if p.1 < p.2 then discountedAt q p.1 else 0) ∘ fun ω => (U ω, V ω))) μ
      exact (hpm.comp_aemeasurable (hU.prodMk hV)).aestronglyMeasurable) 1
      (Eventually.of_forall fun ω => by
        by_cases hlt : U ω < V ω
        · rw [if_pos hlt]
          exact dn q hq (U ω)
        · rw [if_neg hlt]
          norm_num)
  exact ⟨hdi, hpi⟩
