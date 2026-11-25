-- Prove2me | solution 1 for GlobalTheory.CosetEuler.shift_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:34.49915+00:00
-- url     : https://prove2.me/submissions/9895d9a4-666f-4687-9566-ba643eadd3d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumCosetsEulerProduct
import Theorems.Thm_GlobalTheory_CosetEuler_e_mem_J

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
theorem _root_.solution {E : Type} {e : ∀ v, L v →* G} {p : ∀ v, G →* L v} {K : ∀ v, Subgroup (L v)}
    {J H : Subgroup G}
    (hpe : ∀ v a, p v (e v a) = a) (hpe' : ∀ u v, u ≠ v → ∀ a, p u (e v a) = 1)
    (he : ∀ v a, e v a ∈ H) (hJ : ∀ g ∈ H, g ∈ J ↔ ∀ v, p v g ∈ K v) (f : G → E)
    (hf : ∀ g ∈ H, ∀ k ∈ J, f (g * k) = f g) (v : ι) {g : G} (hg : g ∈ H) (hv : p v g ∈ K v) :
    f (shift e p v g) = f g := by
  rw [shift, ← map_inv]
  exact hf g hg _ (e_mem_J hpe hpe' he hJ v _ ((K v).inv_mem hv))
end GlobalTheory.CosetEuler
