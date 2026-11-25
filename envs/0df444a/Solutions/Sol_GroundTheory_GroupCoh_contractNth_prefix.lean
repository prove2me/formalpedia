-- Prove2me | solution 1 for GroundTheory.GroupCoh.contractNth_prefix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:54.064341+00:00
-- url     : https://prove2.me/submissions/6136cd9b-403e-4ac3-a94d-fc295c7285ed

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
theorem _root_.solution {m p : ℕ} (op : α → α → α) (x : Fin (m + 1) → α) (j : Fin (m + 1))
    (j' : Fin (p + 1)) (hp : p ≤ m) (hj : (j : ℕ) = j') :
    (fun l : Fin p => Fin.contractNth j op x ⟨l, by omega⟩) =
      Fin.contractNth j' op (fun l : Fin (p + 1) => x ⟨l, by omega⟩) := by
  funext l
  simp only [Fin.contractNth, Fin.castSucc_mk, Fin.succ_mk, hj]
  rfl
end GroundTheory.GroupCoh
