-- Prove2me | solution 1 for Kyprianou.Ch04.workloadsEventuallyAgree
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:27:25.082716+00:00
-- url     : https://prove2.me/submissions/3ae54674-baeb-4deb-bc3b-9f498c1e5894

import Mathlib
open Filter Set MeasureTheory
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    (w : ℝ) (S X : NNReal → ℝ)
    (hS : Tendsto S atTop atTop) :
    (fun t => max w (S t) - X t) =ᶠ[atTop] (fun t => S t - X t) := by
  filter_upwards [tendsto_atTop.1 hS w] with t ht
  rw [max_eq_right ht]
