-- Prove2me | solution 1 for MultiPeriod.measurable_projX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:47.058796+00:00
-- url     : https://prove2.me/submissions/201274aa-68b1-4faa-b33a-7a88f05f29b4

import Definitions.Def_BicausalOT_MultiPeriod
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_BicausalOT_MultiPeriodTopology

set_option autoImplicit false
open MeasureTheory
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable {X Y}
namespace MultiPeriod
theorem _root_.solution : ∀ t, Measurable (projX (X := X) (Y := Y) t)
  | 0 => measurable_fst
  | t + 1 =>
    ((solution t).comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)
end MultiPeriod
