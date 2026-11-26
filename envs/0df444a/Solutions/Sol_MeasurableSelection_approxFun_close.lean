-- Prove2me | solution 1 for MeasurableSelection.approxFun_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:55.81604+00:00
-- url     : https://prove2.me/submissions/b6c4b36d-aa44-49a1-b5fd-d76efb4faedf

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
    (Φ a ∩ ball (approxFun hu hne hΦ n a) ((1 / 2 : ℝ) ^ n)).Nonempty :=
  (approx hu hne hΦ n).2.2 a
end MeasurableSelection
