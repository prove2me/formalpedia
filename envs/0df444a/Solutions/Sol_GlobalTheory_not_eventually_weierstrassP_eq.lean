-- Prove2me | solution 1 for GlobalTheory.not_eventually_weierstrassP_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:07.226636+00:00
-- url     : https://prove2.me/submissions/02a91e04-a603-4545-9372-d7dee9f77408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Theorems.Thm_GlobalTheory_tendsto_weierstrassP_cobounded

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
theorem _root_.solution {l : ℂ} (hl : l ∈ L.lattice) {g : ℂ → ℂ}
    (hg : ContinuousAt g l) : ¬ ∀ᶠ z in 𝓝[≠] l, ℘[L] z = g z := fun h ↦
  ((tendsto_weierstrassP_cobounded L hl).congr' h).not_tendsto
    (Metric.disjoint_cobounded_nhds (g l)) (hg.tendsto.mono_left nhdsWithin_le_nhds)
end GlobalTheory
