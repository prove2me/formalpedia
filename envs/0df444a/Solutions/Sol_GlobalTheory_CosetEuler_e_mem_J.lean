-- Prove2me | solution 1 for GlobalTheory.CosetEuler.e_mem_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:50:33.296065+00:00
-- url     : https://prove2.me/submissions/f71f7913-bc8f-4808-bfa7-23a3aa155c10

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
theorem _root_.solution {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)} {J H : Subgroup G}
    (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v)
    (v : ι) (k : L v) (hk : k ∈ K v) : e v k ∈ J := by
  refine (hJ _ (he v k)).2 fun u => ?_
  by_cases h : u = v
  · subst h; rw [hpe]; exact hk
  · rw [hpe' u v h]; exact (K u).one_mem
end GlobalTheory.CosetEuler
