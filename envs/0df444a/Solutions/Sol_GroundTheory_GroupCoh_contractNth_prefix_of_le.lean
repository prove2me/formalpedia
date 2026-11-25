-- Prove2me | solution 1 for GroundTheory.GroupCoh.contractNth_prefix_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:54.634078+00:00
-- url     : https://prove2.me/submissions/f18e9872-813d-4016-a167-8ebcf796116e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupCochains

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory MonoidalCategory TensorProduct
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {M : Type*} [Monoid M]
variable {α : Type*}
namespace GroundTheory.GroupCoh
theorem _root_.solution {m p : ℕ} (op : α → α → α) (x : Fin (m + 1) → α)
    (j : Fin (m + 1)) (hj : p ≤ (j : ℕ)) :
    (fun l : Fin p => Fin.contractNth j op x ⟨l, by omega⟩) = fun l : Fin p => x ⟨l, by omega⟩ := by
  funext l
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
  rfl
end GroundTheory.GroupCoh
