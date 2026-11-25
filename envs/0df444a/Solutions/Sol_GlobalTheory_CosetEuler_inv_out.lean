-- Prove2me | solution 1 for GlobalTheory.CosetEuler.inv_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:56.099162+00:00
-- url     : https://prove2.me/submissions/9cb4035b-1ba3-4134-9a33-b345065a4e66

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
theorem _root_.solution {E : Type} {J H : Subgroup G} (hJH : J ≤ H) (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (g : H) :
    f (((g : H ⧸ J.subgroupOf H).out : H) : G) = f g := by
  obtain ⟨k, hk, h⟩ := out_mul hJH g
  rw [h, hf _ g.2 _ hk]
end GlobalTheory.CosetEuler
