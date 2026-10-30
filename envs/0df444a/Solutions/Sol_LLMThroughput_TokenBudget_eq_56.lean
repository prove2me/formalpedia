-- Prove2me | solution 1 for LLMThroughput.TokenBudget.eq_56
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:28:32.915977+00:00
-- url     : https://prove2.me/submissions/6c35c8c5-b372-4cae-b167-5c3ffeec52c5

import Mathlib
import Definitions.Def_LLMThroughput_TokenBudget_Model

open MeasureTheory ProbabilityTheory Filter Topology
open LLMThroughput.TokenBudget

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (vpmax vdmax : ℕ) (a : ℕ → Ω → ℕ) (v : ℕ → Ω → ℕ × ℕ)
    (hA : IIDArrivals μ a v vpmax vdmax) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (arrivalsBefore (fun m => a m ω) n : ℝ) / n) atTop
          (𝓝 (arrivalRate μ a)) ∧
        Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((v i ω).1 : ℝ)) / N) atTop
          (𝓝 (meanPrefill μ v)) ∧
        Tendsto (fun N : ℕ => (∑ i ∈ Finset.range N, ((v i ω).2 : ℝ)) / N) atTop
          (𝓝 (meanDecode μ v)) := by
  -- arrivals
  have h1 := strong_law_ae_real (μ := μ) (fun n ω => (a n ω : ℝ)) hA.integrable_a
    (fun i j hij => (hA.indep_a.indepFun hij).comp (measurable_from_nat (f := fun n : ℕ => (n : ℝ))) (measurable_from_nat (f := fun n : ℕ => (n : ℝ))))
    (fun i => (hA.ident_a i).comp (measurable_from_nat (f := fun n : ℕ => (n : ℝ))))
  -- prefill sizes
  have hvp_meas : ∀ i, Measurable (fun ω => ((v i ω).1 : ℝ)) :=
    fun i => (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_fst.comp (hA.meas_v i))
  have hvd_meas : ∀ i, Measurable (fun ω => ((v i ω).2 : ℝ)) :=
    fun i => (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp (measurable_snd.comp (hA.meas_v i))
  have hint_p : Integrable (fun ω => ((v 0 ω).1 : ℝ)) μ := by
    refine Integrable.of_bound (C := (vpmax : ℝ)) (hvp_meas 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have := (hA.size_bounds 0 ω).2.1
    simp only [Real.norm_natCast]; exact_mod_cast this
  have hint_d : Integrable (fun ω => ((v 0 ω).2 : ℝ)) μ := by
    refine Integrable.of_bound (C := (vdmax : ℝ)) (hvd_meas 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    have := (hA.size_bounds 0 ω).2.2.2
    simp only [Real.norm_natCast]; exact_mod_cast this
  have h2 := strong_law_ae_real (μ := μ) (fun i ω => ((v i ω).1 : ℝ)) hint_p
    (fun i j hij => (hA.indep_v.indepFun hij).comp ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_fst)
      ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_fst))
    (fun i => (hA.ident_v i).comp ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_fst))
  have h3 := strong_law_ae_real (μ := μ) (fun i ω => ((v i ω).2 : ℝ)) hint_d
    (fun i j hij => (hA.indep_v.indepFun hij).comp ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_snd)
      ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_snd))
    (fun i => (hA.ident_v i).comp ((measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp measurable_snd))
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  refine ⟨?_, e2, e3⟩
  simpa [arrivalsBefore, arrivalRate] using e1
