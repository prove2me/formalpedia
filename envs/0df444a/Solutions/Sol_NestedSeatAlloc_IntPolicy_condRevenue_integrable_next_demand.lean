-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.condRevenue_integrable_next_demand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T15:06:59.287445+00:00
-- url     : https://prove2.me/submissions/239d39c7-91cd-47a0-b53c-8468cb9691af

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_prefixRevenueRebuild
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integrable_product_prefix_revenue
import Theorems.Thm_NestedSeatAlloc_IntPolicy_condRevenue_eq_integral_actual_prefix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (k : ℕ) (s : ℝ) (hs : 0 ≤ s)
    (hsU : SFinite (Measure.map
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) :
    Integrable (fun y => condRevenue P X f p (k + 1) y s)
      (Measure.map (X (k + 1)) P) := by
  letI : SFinite (Measure.map
    (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P) := hsU
  have hF := integrable_product_prefix_revenue
    P X f p hM hp k s hs
  have hG : Integrable
      (fun y : ℝ =>
        ∫ u : (Finset.Icc 1 k → ℝ),
          revenue f p (prefixRevenueRebuild k (y, u)) (k + 1) s
            ∂(Measure.map
              (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P))
      (Measure.map (X (k + 1)) P) := hF.integral_prod_left
  have hEq : (fun y : ℝ =>
        ∫ u : (Finset.Icc 1 k → ℝ),
          revenue f p (prefixRevenueRebuild k (y, u)) (k + 1) s
            ∂(Measure.map
              (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω) P)) =
      (fun y : ℝ => condRevenue P X f p (k + 1) y s) := by
    funext y
    exact condRevenue_eq_integral_actual_prefix P X f p hM k y s
  rw [hEq] at hG
  exact hG
