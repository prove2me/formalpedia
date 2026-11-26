-- Prove2me | solution 1 for MeasurableSelection.exists_measurable_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:56.913525+00:00
-- url     : https://prove2.me/submissions/ae0605e9-50d4-4c62-b8e2-1aa5de7ad875

import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_Solution
import Theorems.Thm_exists_measurable_selection

section
open TopologicalSpace
namespace MeasurableSelection
private theorem krm_selection_delegate {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a :=
  _root_.exists_measurable_selection hne hclosed hmeas
end MeasurableSelection
end

set_option autoImplicit false
open TopologicalSpace
open MeasurableSelection
namespace MeasurableSelection
theorem _root_.solution {α : Type*} [MeasurableSpace α] {Y : Type*}
    [MetricSpace Y] [SeparableSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] {Φ : α → Set Y} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set Y, IsOpen U → MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → Y, Measurable f ∧ ∀ a, f a ∈ Φ a :=
  krm_selection_delegate hne hclosed hmeas
end MeasurableSelection
