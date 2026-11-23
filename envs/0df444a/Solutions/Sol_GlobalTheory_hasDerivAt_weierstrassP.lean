-- Prove2me | solution 1 for GlobalTheory.hasDerivAt_weierstrassP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:39.668808+00:00
-- url     : https://prove2.me/submissions/f25dc379-9bdc-4e59-b17b-16b32982ca04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by
  simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
end GlobalTheory
