-- Prove2me | solution 1 for GlobalTheory.analyticAt_weierstrassP_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.126114+00:00
-- url     : https://prove2.me/submissions/45840489-3c3b-4ea6-8c81-3346aee0c947

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
theorem _root_.solution (c : ℂ) {z : ℂ} (hz : z + c ∉ L.lattice) :
    AnalyticAt ℂ (fun t ↦ ℘[L] (t + c)) z :=
  (L.analyticOnNhd_weierstrassP _ hz).comp (f := (· + c)) (by fun_prop)
end GlobalTheory
