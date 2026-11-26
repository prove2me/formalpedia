-- Prove2me | solution 1 for MultiPeriod.continuous_projX
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:16:15.730335+00:00
-- url     : https://prove2.me/submissions/07b226b9-d6ea-4a98-938f-20ebd0592644

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
theorem _root_.solution : ∀ t, Continuous (projX (X := X) (Y := Y) t)
  | 0 => continuous_fst
  | t + 1 =>
    ((solution t).comp continuous_fst).prodMk
      (continuous_fst.comp continuous_snd)
end MultiPeriod
