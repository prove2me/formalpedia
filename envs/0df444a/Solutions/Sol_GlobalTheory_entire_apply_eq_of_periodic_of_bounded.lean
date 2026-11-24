-- Prove2me | solution 1 for GlobalTheory.entire_apply_eq_of_periodic_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:33.789132+00:00
-- url     : https://prove2.me/submissions/8055dc3e-b7f0-4152-bf9d-0069270faa8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Metric Filter Topology
open scoped Nat
open GlobalTheory
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory
theorem _root_.solution [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) {G K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  refine entire_apply_eq_of_periodic_of_compact hF hK.isCompact_closure (fun x => ?_) hper z w
  obtain ⟨k, hk, g, hg, h⟩ := hcov x
  exact ⟨k, subset_closure hk, g, hg, h⟩
end GlobalTheory
