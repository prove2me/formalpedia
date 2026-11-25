-- Prove2me | solution 1 for GlobalTheory.CosetEuler.mem_offSet_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:51.641965+00:00
-- url     : https://prove2.me/submissions/e57c0279-f72c-4b4f-bab7-d5dab99c6c32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_out_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CosetEuler
variable {G ι : Type} [Group G] {L : ι → Type} [∀ v, Group (L v)]
namespace GlobalTheory.CosetEuler
theorem _root_.solution {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hJH : J ≤ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (T : Finset ι) (g : H) :
    (g : H ⧸ J.subgroupOf H) ∈ offSet p K J H T ↔ ∀ v ∉ T, p v g ∈ K v := by
  obtain ⟨k, hk, h⟩ := out_mul hJH g
  have hk' := (hJ k (hJH hk)).1 hk
  simp only [offSet, Set.mem_setOf_eq, h, map_mul]
  exact forall₂_congr fun v _ => Subgroup.mul_mem_cancel_right _ (hk' v)
end GlobalTheory.CosetEuler
