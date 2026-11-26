-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49TruncatedWaitSLLNV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:07:59.424812+00:00
-- url     : https://prove2.me/submissions/90a1c10c-0b26-4ab4-91d1-a2bcb3766876

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
variable {Ω : Type} [MeasurableSpace Ω]
theorem solution (P : Measure Ω) [IsProbabilityMeasure P] (τ : ℕ → Ω → ℝ)
    (hm : ∀ n, Measurable (τ n)) (hi : iIndepFun τ P)
    (hl : ∀ n, IdentDistrib (τ n) (τ 0) P P)
    (hp : ∀ᵐ w ∂P, ∀ n, 0 < τ n w) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ w ∂P, ∃ N : ℕ, ∀ n ≥ N,
      c * (n : ℝ) ≤ ∑ i ∈ Finset.range n, τ i w := by
  let f : ℝ → ℝ := fun x => min 1 (max 0 x)
  let V : ℕ → Ω → ℝ := fun n w => f (τ n w)
  have hf : Measurable f := measurable_const.min (measurable_const.max measurable_id)
  have hV : ∀ n, Measurable (V n) := fun n => hf.comp (hm n)
  have hnon : ∀ x, 0 ≤ f x := fun x => le_min zero_le_one (le_max_left _ _)
  have hbound : Integrable (V 0) P := (integrable_const (1 : ℝ)).mono' (hV 0).aestronglyMeasurable
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hnon _)]; exact min_le_left _ _)
  have hpos : ∀ᵐ w ∂P, 0 < V 0 w := hp.mono fun w hw => lt_min zero_lt_one (lt_of_lt_of_le (hw 0) (le_max_right _ _))
  have hmean : 0 < ∫ w, V 0 w ∂P := by
    apply (integral_pos_iff_support_of_nonneg (fun w => hnon (τ 0 w)) hbound).2
    have hs : MeasurableSet (Function.support (V 0)) := (hV 0) (measurableSet_singleton (0 : ℝ)).compl
    have he := (ae_mem_iff_measure_eq hs.nullMeasurableSet).1 (hpos.mono fun w hw => ne_of_gt hw)
    rw [he, measure_univ]
    exact zero_lt_one
  have hind : iIndepFun V P := hi.comp (fun _ => f) (fun _ => hf)
  have hlim := strong_law_ae_real V hbound (fun _ _ h => hind.indepFun h) (fun n => (hl n).comp hf)
  refine ⟨(∫ w, V 0 w ∂P) / 2, by linarith, ?_⟩
  filter_upwards [hp, hlim] with w hw hlimw
  have he := hlimw.eventually (Ioi_mem_nhds (show (∫ w, V 0 w ∂P) / 2 < ∫ w, V 0 w ∂P by linarith))
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N 1) hn))
  have hv := hN n (le_trans (le_max_left N 1) hn)
  have hsum : (∑ i ∈ Finset.range n, V i w) ≤ ∑ i ∈ Finset.range n, τ i w :=
    Finset.sum_le_sum fun i _ => (min_le_right _ _).trans (by rw [max_eq_right (hw i).le])
  exact (le_of_lt ((lt_div_iff₀ hnpos).1 hv)).trans hsum
