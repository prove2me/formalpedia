-- Prove2me | solution 1 for MultiPeriod.continuous_projY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:21.776276+00:00
-- url     : https://prove2.me/submissions/dabd62a5-85cf-4725-bd46-1830efb66c37

import Definitions.Def_BicausalOT_MultiPeriod
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_BicausalOT_MultiPeriodTopology

set_option autoImplicit false
open MeasureTheory
noncomputable section
open MultiPeriod
variable (X Y : ℕ → Type*)
variable [∀ n, TopologicalSpace (X n)] [∀ n, TopologicalSpace (Y n)]
variable {X Y}
namespace MultiPeriod
theorem _root_.solution : ∀ t, Continuous (projY (X := X) (Y := Y) t)
  | 0 => continuous_snd
  | t + 1 =>
    ((solution t).comp continuous_fst).prodMk
      (continuous_snd.comp continuous_snd)
end MultiPeriod
