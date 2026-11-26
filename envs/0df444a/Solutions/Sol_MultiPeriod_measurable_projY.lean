-- Prove2me | solution 1 for MultiPeriod.measurable_projY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:14:50.065328+00:00
-- url     : https://prove2.me/submissions/9f1fab7b-70b7-479b-8377-0797eff4e142

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
theorem _root_.solution : ∀ t, Measurable (projY (X := X) (Y := Y) t)
  | 0 => measurable_snd
  | t + 1 =>
    ((solution t).comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
end MultiPeriod
