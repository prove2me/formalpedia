-- Prove2me | solution 1 for MeasurableSelection.approxFun_dist_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:54.737138+00:00
-- url     : https://prove2.me/submissions/ce1f4af7-1f84-4f51-8261-8967510f8d74

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Theorems.Thm_MeasurableSelection_approx_succ_spec

set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}
namespace MeasurableSelection
theorem _root_.solution (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    dist (approxFun hu hne hΦ n a) (approxFun hu hne hΦ (n + 1) a) ≤
      (3 / 2 : ℝ) * (1 / 2) ^ n := by
  obtain ⟨y, hyΦ, hy1, hy2⟩ := approx_succ_spec hu hne hΦ n a
  calc dist (approxFun hu hne hΦ n a) (approxFun hu hne hΦ (n + 1) a) ≤
      dist y (approxFun hu hne hΦ n a) + dist y (approxFun hu hne hΦ (n + 1) a) :=
        dist_triangle_left _ _ _
    _ ≤ (1 / 2 : ℝ) ^ n + (1 / 2) ^ (n + 1) :=
        add_le_add (mem_ball.mp hy2).le (mem_ball.mp hy1).le
    _ = (3 / 2 : ℝ) * (1 / 2) ^ n := by rw [pow_succ]; ring
end MeasurableSelection
