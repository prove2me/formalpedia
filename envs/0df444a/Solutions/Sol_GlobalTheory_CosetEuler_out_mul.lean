-- Prove2me | solution 1 for GlobalTheory.CosetEuler.out_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:51:49.062632+00:00
-- url     : https://prove2.me/submissions/f8ae0dcd-439a-4f69-b650-3083a959b467

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
theorem _root_.solution {J H : Subgroup G} (hJH : J ≤ H) (g : H) :
    ∃ k ∈ J, (((g : H ⧸ J.subgroupOf H).out : H) : G) = g * k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (J.subgroupOf H) g
  exact ⟨((k : H) : G), Subgroup.mem_subgroupOf.1 k.2, by rw [hk]; rfl⟩
end GlobalTheory.CosetEuler
