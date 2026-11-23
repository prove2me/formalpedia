-- Prove2me | solution 1 for GlobalTheory.eqOn_compl_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:58.126965+00:00
-- url     : https://prove2.me/submissions/7a89f431-4b42-4a6b-88f2-d6df6903ceaf

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
theorem _root_.solution {f g : ℂ → ℂ} {S : Set ℂ} (hS : S.Countable)
    (hf : AnalyticOnNhd ℂ f Sᶜ) (hg : AnalyticOnNhd ℂ g Sᶜ) {z : ℂ} (hz : z ∉ S)
    (h : f =ᶠ[𝓝 z] g) : Set.EqOn f g Sᶜ :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hS).2 hz h
end GlobalTheory
