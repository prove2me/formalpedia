-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.expRevenue_eq_integral_condRevenue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:14:55.274021+00:00
-- url     : https://prove2.me/submissions/6f480f90-8f07-45b0-afc2-7c0186d1cb62

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_measurable_prefix_vector
import Theorems.Thm_measurable_prefixRevenueRebuild
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_actual_prefix_rebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_prefix_next_joint_product_law
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integrable_product_prefix_revenue
import Theorems.Thm_NestedSeatAlloc_IntPolicy_product_law_integral_nested_sfinite
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_eq_integral_actual_prefix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (hs : 0 ≤ s) :
    expRevenue P X f p (k + 1) s =
      ∫ y : ℝ, condRevenue P X f p (k + 1) y s
        ∂(Measure.map (X (k + 1)) P) := by
  letI : IsProbabilityMeasure P := hM.isProb
  let U : Ω → (Finset.Icc 1 k → ℝ) := fun ω i => X i.1 ω
  let Z : Ω → ℝ := X (k + 1)
  let F : ℝ × (Finset.Icc 1 k → ℝ) → ℝ :=
    fun z => revenue f p (prefixRevenueRebuild k z) (k + 1) s
  have hU : Measurable U := measurable_prefix_vector P X f hM k
  have hZ : Measurable Z := hM.meas (k + 1)
  have hsU : SFinite (Measure.map U P) := by infer_instance
  have hsZ : SFinite (Measure.map Z P) := by infer_instance
  have hF : Measurable F :=
    (revenue_joint_measurable f p (k + 1)).comp
      ((measurable_prefixRevenueRebuild k).prodMk measurable_const)
  have hJoint :
      Measure.map (fun ω => (Z ω, U ω)) P =
        (Measure.map Z P).prod (Measure.map U P) :=
    prefix_next_joint_product_law P X f hM k
  have hInt :
      Integrable F ((Measure.map Z P).prod (Measure.map U P)) :=
    integrable_product_prefix_revenue P X f p hM hp k s hs
  have hProduct :=
    product_law_integral_nested_sfinite P U Z hU hZ
      hsU hsZ F hF hJoint hInt
  have hCond (y : ℝ) :
      (∫ u, F (y, u) ∂Measure.map U P) =
        condRevenue P X f p (k + 1) y s :=
    condRevenue_eq_integral_actual_prefix P X f p hM k y s
  have hActualPointwise (ω : Ω) :
      revenue f p (fun i => X i ω) (k + 1) s =
        F (Z ω, U ω) :=
    revenue_actual_prefix_rebuild X f p k ω s
  have hActual :
      expRevenue P X f p (k + 1) s =
        ∫ ω, F (Z ω, U ω) ∂P := by
    unfold expRevenue
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hActualPointwise
  have hIntegrals :
      (∫ y, ∫ u, F (y, u) ∂Measure.map U P ∂Measure.map Z P) =
        (∫ y, condRevenue P X f p (k + 1) y s ∂Measure.map Z P) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => hCond y)
  calc
    expRevenue P X f p (k + 1) s =
        ∫ ω, F (Z ω, U ω) ∂P := hActual
    _ = ∫ y, ∫ u, F (y, u) ∂Measure.map U P ∂Measure.map Z P :=
      hProduct
    _ = ∫ y, condRevenue P X f p (k + 1) y s
      ∂Measure.map Z P := hIntegrals
