-- Prove2me | solution 1 for GlobalTheory.Conv.coe_expandConv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:32.936681+00:00
-- url     : https://prove2.me/submissions/9ad3ecfd-d20e-4235-b3ce-e52d3f0ee09a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
variable (k : ℕ) (hk : k ≠ 0)
namespace GlobalTheory.Conv
theorem _root_.solution (g : convSeries) :
    (expandConv k hk g : ℂ⟦X⟧) = PowerSeries.expand k hk g := rfl
end GlobalTheory.Conv
