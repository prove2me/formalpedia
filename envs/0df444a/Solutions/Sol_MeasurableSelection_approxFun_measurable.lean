-- Prove2me | solution 1 for MeasurableSelection.approxFun_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:09:58.84797+00:00
-- url     : https://prove2.me/submissions/6bf5246b-1ea8-4696-8066-cf392149a961

import Mathlib
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection

set_option autoImplicit false
open Metric Set Filter Topology TopologicalSpace
open MeasurableSelection
variable {α : Type*} [MeasurableSpace α]
variable {Y : Type*} [MetricSpace Y] {Φ : α → Set Y} {u : ℕ → Y}
namespace MeasurableSelection
theorem _root_.solution [MeasurableSpace Y] (hu : DenseRange u)
    (hne : ∀ a, (Φ a).Nonempty)
    (hΦ : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) (n : ℕ) :
    Measurable (approxFun hu hne hΦ n) :=
  (Measurable.of_discrete (f := u)).comp (approx hu hne hΦ n).2.1
end MeasurableSelection
