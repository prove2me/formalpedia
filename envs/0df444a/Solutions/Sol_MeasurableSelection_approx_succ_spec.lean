-- Prove2me | solution 1 for MeasurableSelection.approx_succ_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:55.211123+00:00
-- url     : https://prove2.me/submissions/5fd0a75a-2651-458f-8f82-a53ab698877e

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection

set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}
namespace MeasurableSelection
theorem _root_.solution (hu : DenseRange u) (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty})
    (n : ℕ) (a : α) :
    (Φ a ∩ (ball (u ((approx hu hne hΦ (n + 1)).1 a)) ((1 / 2 : ℝ) ^ (n + 1)) ∩
      ball (u ((approx hu hne hΦ n).1 a)) ((1 / 2 : ℝ) ^ n))).Nonempty :=
  stepFun_spec hu (approx hu hne hΦ n).2.2 (pow_pos one_half_pos (n + 1)) a
end MeasurableSelection
