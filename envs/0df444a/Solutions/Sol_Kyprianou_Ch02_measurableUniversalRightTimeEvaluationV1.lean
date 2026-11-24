-- Prove2me | solution 1 for Kyprianou.Ch02.measurableUniversalRightTimeEvaluationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:52:35.756027+00:00
-- url     : https://prove2.me/submissions/d51aeea5-4761-4651-991f-fa7ef433c0a8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution :
    ∃ E : (ℝ≥0 → ℝ) × ℝ≥0 → ℝ, Measurable E ∧
      ∀ (f : ℝ≥0 → ℝ), (∀ t, ContinuousWithinAt f (Ici t) t) →
        ∀ t, E (f, t) = f t := by
  let c : ℕ → ℝ≥0 → ℝ≥0 := fun n t => (⌈t * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n
  have hge : ∀ n t, t ≤ c n t := by
    intro n t
    simp only [c]
    rw [le_div_iff₀ (by positivity)]
    exact Nat.le_ceil _
  have hle : ∀ n t, c n t ≤ t + 1 / 2 ^ n := by
    intro n t
    simp only [c]
    rw [div_le_iff₀ (by positivity), add_mul, one_div,
      inv_mul_cancel₀ (by positivity)]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hmeas (n : ℕ) : Measurable (fun p : (ℝ≥0 → ℝ) × ℝ≥0 => p.1 (c n p.2)) := by
    have hGrid : Measurable (fun p : (ℝ≥0 → ℝ) × ℕ =>
        p.1 ((p.2 : ℝ≥0) / 2 ^ n)) :=
      measurable_from_prod_countable_left (fun k =>
        measurable_pi_apply ((k : ℝ≥0) / 2 ^ n))
    exact hGrid.comp (measurable_fst.prodMk (Nat.measurable_ceil.comp
      (measurable_snd.mul_const _)))
  refine ⟨fun p => Filter.limsup (fun n => p.1 (c n p.2)) atTop,
    Measurable.limsup hmeas, ?_⟩
  intro f hf t
  have ht : Tendsto (fun n => c n t) atTop (𝓝[Ici t] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun n => hge n t)⟩
    have hlim : Tendsto (fun n : ℕ => t + 1 / (2 : ℝ≥0) ^ n) atTop (𝓝 t) := by
      have hzero : Tendsto (fun n : ℕ => (1 : ℝ≥0) / 2 ^ n) atTop (𝓝 0) := by
        simp only [one_div, ← inv_pow]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using tendsto_const_nhds.add hzero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (hge · t) (hle · t)
  exact ((hf t).tendsto.comp ht).limsup_eq
