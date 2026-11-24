-- Prove2me | solution 1 for Kyprianou.Ch02.vectorCharFunctionPointwiseLimitLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:23:29.000934+00:00
-- url     : https://prove2.me/submissions/11a3fcf7-5066-4089-ac6a-dc6e2e24b7e1

import Mathlib
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (d : ℕ) (μ : ℕ → Measure (Fin d → ℝ))
    (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (f : (Fin d → ℝ) → ℂ) (hf : ContinuousAt f 0)
    (h : ∀ θ : Fin d → ℝ,
      Tendsto (fun n => (∫ x, Complex.exp (Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂(μ n))) atTop (nhds (f θ))) :
    ∃ m : Measure (Fin d → ℝ), IsProbabilityMeasure m ∧
      ∀ θ : Fin d → ℝ, (∫ x, Complex.exp (Complex.I * (((∑ i : Fin d, θ i * x i : ℝ)) : ℂ)) ∂m) = f θ := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let e : E ≃L[ℝ] (Fin d → ℝ) := PiLp.continuousLinearEquiv 2 ℝ _
  let fE : E → ℂ := fun z => f (e z)
  letI : ∀ n, IsProbabilityMeasure (μ n) := hμ
  let μE (n : ℕ) : Measure E := (μ n).map e.symm
  letI (n : ℕ) : IsProbabilityMeasure (μE n) :=
    Measure.isProbabilityMeasure_map e.symm.continuous.measurable.aemeasurable
  have hmap (m : Measure (Fin d → ℝ)) (z : E) :
      charFun (m.map e.symm) z =
        ∫ x, Complex.exp (Complex.I *
          (((∑ i : Fin d, e z i * x i : ℝ)) : ℂ)) ∂m := by
    rw [charFun_apply, integral_map e.symm.continuous.measurable.aemeasurable]
    · apply integral_congr_ae
      filter_upwards [] with x
      rw [PiLp.inner_apply]
      simp only [Real.inner_apply]
      change Complex.exp (↑(∑ i : Fin d, x i * e z i) * Complex.I) = _
      simp only [mul_comm]
    · fun_prop
  have hfE : ContinuousAt fE 0 := by
    have he : Tendsto e (nhds 0) (nhds 0) := by
      have h := e.continuous.continuousAt (x := (0 : E))
      change Tendsto e (nhds 0) (nhds (e 0)) at h
      simpa only [map_zero] using h
    exact hf.tendsto.comp he
  have hE (z : E) : Tendsto (fun n => charFun (μE n) z)
      atTop (nhds (fE z)) := by
    simpa only [μE, hmap, fE] using h (e z)
  let p (n : ℕ) : ProbabilityMeasure E := ⟨μE n, inferInstance⟩
  have ht := isTightMeasureSet_of_tendsto_charFun hfE hE
  have hcompact : IsCompact (closure (Set.range p)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have hs : {m : Measure E | ∃ q ∈ Set.range p, (q : Measure E) = m} =
        Set.range μE := by
      ext m
      constructor
      · rintro ⟨q, ⟨n, rfl⟩, hq⟩
        exact ⟨n, hq⟩
      · rintro ⟨n, rfl⟩
        exact ⟨p n, ⟨n, rfl⟩, rfl⟩
    rw [hs]
    exact ht
  obtain ⟨q, _, k, hk, hq⟩ := hcompact.isSeqCompact
    (fun n => subset_closure (Set.mem_range_self n))
  have hqchar (z : E) : charFun (q : Measure E) z = fE z := by
    have h1 := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hq) z
    have h2 := (hE z).comp hk.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  let m := (q : Measure E).map e
  refine ⟨m, Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable, ?_⟩
  intro θ
  have hback : m.map e.symm = (q : Measure E) := by
    rw [show m = (q : Measure E).map e from rfl,
      Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
    simp
  have hz := hmap m (e.symm θ)
  rw [hback, e.apply_symm_apply] at hz
  exact hz.symm.trans (by simpa [fE] using hqchar (e.symm θ))
