-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.integrable_product_prefix_revenue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:06:12.70395+00:00
-- url     : https://prove2.me/submissions/3eeb1b32-4792-49b0-a375-44a1e1576eb1

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
import Theorems.Thm_revenue_integrable_of_seat_model
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_measurable_prefixRevenueRebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_measurable_prefix_vector
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_actual_prefix_rebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_prefix_next_joint_product_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable
      (fun z : ℝ × (Finset.Icc 1 k → ℝ) =>
        revenue f p (prefixRevenueRebuild k z) (k + 1) s)
      ((Measure.map (X (k + 1)) P).prod
        (Measure.map
          (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) := by
  let U : Ω → (Finset.Icc 1 k → ℝ) := fun ω i => X i.1 ω
  let Z : Ω → ℝ := X (k + 1)
  let F : ℝ × (Finset.Icc 1 k → ℝ) → ℝ :=
    fun z => revenue f p (prefixRevenueRebuild k z) (k + 1) s
  have hU : Measurable U := measurable_prefix_vector P X f hM k
  have hZ : Measurable Z := hM.meas (k + 1)
  have hZU : Measurable (fun ω => (Z ω, U ω)) := hZ.prodMk hU
  have hF : Measurable F :=
    (revenue_joint_measurable f p (k + 1)).comp
      ((measurable_prefixRevenueRebuild k).prodMk measurable_const)
  have hR : Integrable
      (fun ω => revenue f p (fun i => X i ω) (k + 1) s) P :=
    revenue_integrable_of_seat_model P X f p hM hp k s hs
  have hEq :
      (fun ω : Ω => F (Z ω, U ω)) =
      (fun ω => revenue f p (fun i => X i ω) (k + 1) s) := by
    funext ω
    exact (revenue_actual_prefix_rebuild X f p k ω s).symm
  have hPullback : Integrable (fun ω => F (Z ω, U ω)) P := by
    rw [hEq]
    exact hR
  have hMap :
      Integrable F (Measure.map (fun ω => (Z ω, U ω)) P) :=
    (integrable_map_measure hF.aestronglyMeasurable
      hZU.aemeasurable).mpr hPullback
  have hJoint := prefix_next_joint_product_law P X f hM k
  change Integrable F
    (Measure.map
      (fun ω : Ω => (X (k + 1) ω,
        fun i : (Finset.Icc 1 k) => X i.1 ω)) P) at hMap
  rw [hJoint] at hMap
  change Integrable F
    ((Measure.map (X (k + 1)) P).prod
      (Measure.map
        (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P))
  exact hMap
