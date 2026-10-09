-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.prefix_next_joint_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:24:09.263773+00:00
-- url     : https://prove2.me/submissions/28295c7e-8c0b-4618-80d4-8fdb6bfb1743

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_indep_prefix_next_demand
import Theorems.Thm_NestedSeatAlloc_IntPolicy_measurable_prefix_vector

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ)
    (hM : IsSeatModel P X f) (k : ℕ) :
    Measure.map
      (fun ω : Ω => (X (k + 1) ω,
        fun i : (Finset.Icc 1 k) => X i.1 ω)) P =
    (Measure.map (X (k + 1)) P).prod
      (Measure.map
        (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P) := by
  letI : IsProbabilityMeasure P := hM.isProb
  have hInd : IndepFun (X (k + 1))
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P :=
    (indep_prefix_next_demand P X f hM k).symm
  exact (indepFun_iff_map_prod_eq_prod_map_map
    (hM.meas (k + 1)).aemeasurable
    (measurable_prefix_vector P X f hM k).aemeasurable).mp hInd
