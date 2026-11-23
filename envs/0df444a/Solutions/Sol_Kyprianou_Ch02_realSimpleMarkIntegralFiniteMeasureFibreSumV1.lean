-- Prove2me | solution 1 for Kyprianou.Ch02.realSimpleMarkIntegralFiniteMeasureFibreSumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:29:44.501803+00:00
-- url     : https://prove2.me/submissions/00a0b746-5411-4946-bc33-8583eb05eea2

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Integrate a finite-range mark function by summing over its value fibres. -/
theorem solution
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (f : SimpleFunc ℝ ℝ) :
    (∫ z : ℝ × ℝ, f z.2 ∂μ) =
      ∑ x ∈ f.range, (μ {p : ℝ × ℝ | f p.2 = x}).toReal * x := by
  classical
  let g : SimpleFunc (ℝ × ℝ) ℝ :=
    f.comp Prod.snd measurable_snd
  have hrange : g.range = f.range := by
    apply Finset.Subset.antisymm (f.range_comp_subset_range measurable_snd)
    intro y hy
    obtain ⟨x, hx⟩ := SimpleFunc.mem_range.mp hy
    apply SimpleFunc.mem_range.mpr
    refine ⟨((0 : ℝ), x), ?_⟩
    simpa only [g, SimpleFunc.coe_comp, Function.comp_apply] using hx
  have hfunc : (fun z : ℝ × ℝ => f z.2) = g := by
    funext z
    rfl
  rw [hfunc, g.integral_eq_sum (g.integrable_of_isFiniteMeasure), hrange]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [smul_eq_mul, Measure.real_def]
  congr 1
