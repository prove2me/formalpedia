-- Prove2me | solution 1 for GlobalTheory.entire_apply_eq_of_periodic_of_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:47:00.394443+00:00
-- url     : https://prove2.me/submissions/db11e76b-f7bf-44b1-9ac3-1922a876975a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_values_on_compact

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
theorem _root_.solution {F : E → V} (hF : Differentiable ℂ F)
    {G K : Set E} (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by
  refine entire_apply_eq_of_values_on_compact hF hK (fun x => ?_) z w
  obtain ⟨k, hk, g, hg, rfl⟩ := hcov x
  exact ⟨k, hk, hper k g hg⟩
end GlobalTheory
