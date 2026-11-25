-- Prove2me | solution 1 for GroundTheory.GroupCoh.contractNth_suffix_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:55.932617+00:00
-- url     : https://prove2.me/submissions/cad3f33f-a48e-48fa-a770-6c94c8e00417

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
theorem _root_.solution {m p q : ℕ} (op : α → α → α) (x : Fin (m + 1) → α)
    (j : Fin (m + 1)) (hpq : p + q ≤ m) (hj : (j : ℕ) < p) :
    (fun l : Fin q => Fin.contractNth j op x ⟨p + l, by omega⟩) =
      fun l : Fin q => x ⟨p + 1 + l, by omega⟩ := by
  funext l
  rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
  simp only [Fin.succ_mk]
  congr 2
  omega
end GroundTheory.GroupCoh
