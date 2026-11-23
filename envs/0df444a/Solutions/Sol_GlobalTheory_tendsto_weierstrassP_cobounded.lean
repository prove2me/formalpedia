-- Prove2me | solution 1 for GlobalTheory.tendsto_weierstrassP_cobounded
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:44.984926+00:00
-- url     : https://prove2.me/submissions/3b51f390-0449-46d4-8926-16159620a4ee

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
theorem _root_.solution {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto ℘[L] (𝓝[≠] l) (cobounded ℂ) := by
  rw [tendsto_cobounded_iff_meromorphicOrderAt_neg (L.meromorphic_weierstrassP l),
    L.order_weierstrassP l hl]
  decide
end GlobalTheory
