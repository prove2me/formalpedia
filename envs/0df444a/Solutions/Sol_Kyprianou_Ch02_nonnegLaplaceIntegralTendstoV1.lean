-- Prove2me | solution 1 for Kyprianou.Ch02.nonnegLaplaceIntegralTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:26:28.310752+00:00
-- url     : https://prove2.me/submissions/2b25b1f0-348d-4be6-84e3-d61feb432975

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ × ℝ) (f : Ω → ℝ × ℝ)
    (hm : ∀ n, AEMeasurable (F n) P)
    (hn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ (F n ω).1 ∧ 0 ≤ (F n ω).2)
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (f ω)))
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Tendsto (fun n => ∫ ω, Real.exp (-(u*(F n ω).1+v*(F n ω).2)) ∂P) atTop
      (nhds (∫ ω, Real.exp (-(u*(f ω).1+v*(f ω).2)) ∂P)) := by
  let K (p : ℝ × ℝ) := Real.exp (-(u*p.1+v*p.2))
  have hk : Continuous K := by unfold K; fun_prop
  apply tendsto_integral_of_dominated_convergence (fun _ => 1)
  · intro n
    exact (hk.measurable.comp_aemeasurable (hm n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hn n] with ω hw
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (add_nonneg (mul_nonneg hu hw.1) (mul_nonneg hv hw.2))
  · filter_upwards [ht] with ω hw
    exact (hk.continuousAt.tendsto).comp hw
