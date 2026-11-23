-- Prove2me | solution 1 for GlobalTheory.Conv.coe_expandConvLaurent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:25.220887+00:00
-- url     : https://prove2.me/submissions/8ac4b5e8-8b84-45a7-9120-680c3cbfcf9f

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
theorem _root_.solution (f : convLaurent) :
    (expandConvLaurent k hk f : ℂ⸨X⸩) = expandLaurent k hk f := rfl
end GlobalTheory.Conv
