-- Prove2me | solution 1 for GlobalTheory.entire_apply_eq_of_values_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:37:10.820015+00:00
-- url     : https://prove2.me/submissions/08e5d2d3-037b-4aee-8372-bb94c325c2fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal

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
theorem _root_.solution {F : E → V} (hF : Differentiable ℂ F) {K : Set E}
    (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, F x = F k) (z w : E) : F z = F w := by
  refine hF.apply_eq_apply_of_bounded ((hK.image hF.continuous).isBounded.subset ?_) z w
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk, h⟩ := hcov x
  exact ⟨k, hk, h.symm⟩
end GlobalTheory
