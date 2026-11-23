-- Prove2me | solution 1 for GlobalTheory.Conv.expandConv_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:14.688349+00:00
-- url     : https://prove2.me/submissions/fbc11b68-8790-4872-bb37-a5f9a39063bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemPuncturedRingIffPowerSeriesPart
import Theorems.Thm_GlobalTheory_Conv_coe_expandConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Conv.coe_expandConv

set_option autoImplicit false
open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric
noncomputable section
open GlobalTheory GlobalTheory.Conv
variable (k : ℕ) (hk : k ≠ 0)
namespace GlobalTheory.Conv
theorem _root_.solution : expandConv k hk u = u ^ k := Subtype.ext (by simp)
end GlobalTheory.Conv
