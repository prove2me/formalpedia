-- Prove2me | solution 1 for GlobalTheory.CosetEuler.hasSum_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:07.06962+00:00
-- url     : https://prove2.me/submissions/4622f4d1-09bf-413a-82ee-af846887f4b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_inv_out
import Theorems.Thm_GlobalTheory_CosetEuler_offSet_empty

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
variable [DecidableEq ι] {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hJH : J ≤ H) (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
include hJH hJ
namespace GlobalTheory.CosetEuler
theorem _root_.solution {E : Type} [AddCommMonoid E] [TopologicalSpace E] (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) :
    HasSum ((offSet p K J H ∅).indicator fun y => f ((y.out : H) : G)) (f 1) := by
  rw [offSet_empty hJH hJ]
  have := hasSum_single
    (f := ({((1 : H) : H ⧸ J.subgroupOf H)} : Set (H ⧸ J.subgroupOf H)).indicator
      fun y => f ((y.out : H) : G))
    ((1 : H) : H ⧸ J.subgroupOf H) (fun b hb => Set.indicator_of_notMem (Set.mem_singleton_iff.not.2 hb) _)
  rw [Set.indicator_of_mem (Set.mem_singleton _), inv_out hJH f hf] at this
  exact this
end GlobalTheory.CosetEuler
