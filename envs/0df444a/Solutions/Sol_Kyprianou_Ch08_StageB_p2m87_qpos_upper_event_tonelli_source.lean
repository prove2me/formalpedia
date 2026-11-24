-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m87_qpos_upper_event_tonelli_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:05:01.705697+00:00
-- url     : https://prove2.me/submissions/40fee91a-99a2-4fea-a71b-d10398aff90b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m87_qpos_factor_source_exit_clocks_eq
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open Kyprianou.Ch08
open Kyprianou.Ch08.StageB
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = D.X t ω)
    (q a x : ℝ) (A : Set ℝ) (hA : MeasurableSet A) :
    let U := twoSidedExitUpTime X (a - x)
    let L := twoSidedExitDownTime X (-x)
    let τ : Ω → ℝ≥0 := fun ω => (U ω).toNNReal
    let disc : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-q * (t : ℝ)))
    (∫⁻ ω, ∫⁻ t : ℝ≥0, disc t *
      (if U ω ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A
        then 1 else 0) ∂positiveTimeLebesgue ∂P) =
      ∫⁻ t : ℝ≥0, disc t *
        P {ω | (t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
          tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧
          shifted D.X x t ω ∈ A} ∂positiveTimeLebesgue
:= by
  intro U L τ disc
  have hSF : SFinite positiveTimeLebesgue := by unfold positiveTimeLebesgue; infer_instance
  obtain ⟨hU, hL⟩ := chat03_both_named_passage_clocks_measurable X (-x) (a - x)
  have hd : Measurable disc := by dsimp [disc]; fun_prop
  have hj := chat04_levy_joint_time_state_measurable X
  have ht : Measurable (fun z : ℝ≥0 × Ω => (z.1 : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp measurable_fst
  let S : Set (ℝ≥0 × Ω) := {z | U z.2 ≤ (z.1 : ℝ≥0∞) ∧
    (z.1 : ℝ≥0∞) < L z.2 ∧ x + X.X z.1 z.2 ∈ A}
  have hS : MeasurableSet S := (measurableSet_le (hU.comp measurable_snd) ht).inter
    ((measurableSet_lt ht (hL.comp measurable_snd)).inter ((measurable_const.add hj) hA))
  let G : Ω × ℝ≥0 → ℝ≥0∞ := fun z => disc z.2 * (if (z.2, z.1) ∈ S then 1 else 0)
  have hG : Measurable G := (hd.comp measurable_snd).mul
    (Measurable.ite ((measurable_snd.prodMk measurable_fst) hS) measurable_const measurable_const)
  change (∫⁻ ω, ∫⁻ t : ℝ≥0, G (ω,t) ∂positiveTimeLebesgue ∂P) = _
  rw [lintegral_lintegral_swap hG.aemeasurable]
  refine lintegral_congr fun t => ?_
  let C : Set Ω := {ω | (t,ω) ∈ S}
  have hC : MeasurableSet C := (measurable_const.prodMk measurable_id) hS
  have hin : (fun ω => G (ω,t)) = fun ω => disc t * C.indicator 1 ω := by
    funext ω; simp [G, C, Set.indicator_apply]
  rw [hin, lintegral_const_mul' _ _ (by dsimp [disc]; exact ENNReal.ofReal_ne_top),
    lintegral_indicator_one hC]
  congr 1
  apply measure_congr
  filter_upwards [hpath, p2m87_qpos_factor_source_exit_clocks_eq D X hpath x a] with ω hω hc
  apply propext
  change (U ω ≤ (t : ℝ≥0∞) ∧ (t : ℝ≥0∞) < L ω ∧ x + X.X t ω ∈ A) ↔
    ((t : WithTop ℝ≥0) < tauMinus (shifted D.X x) 0 ω ∧
      tauPlus (shifted D.X x) a ω ≤ (t : WithTop ℝ≥0) ∧ shifted D.X x t ω ∈ A)
  obtain ⟨hu, hl, -⟩ := hc
  simp only [shifted, ← hω, hu, hl]
  exact and_left_comm
