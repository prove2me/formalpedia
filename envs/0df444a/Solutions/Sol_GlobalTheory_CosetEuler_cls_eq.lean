-- Prove2me | solution 1 for GlobalTheory.CosetEuler.cls_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:46.966156+00:00
-- url     : https://prove2.me/submissions/ab71f787-0eb5-4f56-83f3-7f5665941e4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct

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
    (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (g h : H) :
    ((g : H ⧸ J.subgroupOf H) = h) ↔ ∀ v, (p v g)⁻¹ * p v h ∈ K v := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hJ _ (g⁻¹ * h).2]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
end GlobalTheory.CosetEuler
