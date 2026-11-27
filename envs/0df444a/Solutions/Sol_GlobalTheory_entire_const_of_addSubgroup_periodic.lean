-- Prove2me | solution 1 for GlobalTheory.entire_const_of_addSubgroup_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:46.480887+00:00
-- url     : https://prove2.me/submissions/c8b30b6e-43ea-46af-9077-3c6708ae7f38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Theorems.Thm_GlobalTheory_entire_apply_eq_of_periodic_of_bounded

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
    (hF : Differentiable ℂ F) (G : AddSubgroup E) {K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ g ∈ G, ∃ k ∈ K, x = g + k)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) : ∃ c, ∀ z, F z = c := by
  refine ⟨F 0, fun z => entire_apply_eq_of_periodic_of_bounded hF (G := G) hK (fun x => ?_)
    hper z 0⟩
  obtain ⟨g, hg, k, hk, h⟩ := hcov x
  exact ⟨k, hk, g, hg, h.trans (add_comm _ _)⟩
end GlobalTheory
