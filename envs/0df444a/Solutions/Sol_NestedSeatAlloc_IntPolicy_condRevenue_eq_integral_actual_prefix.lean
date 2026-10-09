-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.condRevenue_eq_integral_actual_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:27:55.90678+00:00
-- url     : https://prove2.me/submissions/e59b9351-9876-4590-aa79-fd6129e2a120

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_measurable_prefix_vector
import Theorems.Thm_measurable_prefixRevenueRebuild
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_condRevenue_eq_integral_prefix_law
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_frozen_prefix_rebuild

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) (y s : ℝ) :
    (∫ u : (Finset.Icc 1 k → ℝ),
      revenue f p (prefixRevenueRebuild k (y, u)) (k + 1) s
        ∂(Measure.map
          (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) =
      condRevenue P X f p (k + 1) y s := by
  let U : Ω → (Finset.Icc 1 k → ℝ) :=
    fun ω i => X i.1 ω
  have hU : Measurable U := measurable_prefix_vector P X f hM k
  have hRebuild : Measurable (prefixRevenueRebuild k) :=
    measurable_prefixRevenueRebuild k
  have hJoint : ∀ s, Measurable
      (fun z : ℝ × (Finset.Icc 1 k → ℝ) =>
        revenue f p (prefixRevenueRebuild k z) (k + 1) s) := by
    intro s
    exact (revenue_joint_measurable f p (k + 1)).comp
      (hRebuild.prodMk measurable_const)
  have hUpdate : ∀ ω y s,
      revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
      revenue f p (prefixRevenueRebuild k (y, U ω)) (k + 1) s := by
    intro ω y s
    exact revenue_frozen_prefix_rebuild X f p k ω y s
  exact condRevenue_eq_integral_prefix_law P X f p k U
    (prefixRevenueRebuild k) hU hJoint hUpdate y s
