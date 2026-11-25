-- Prove2me | solution 1 for GroundTheory.GroupCoh.contractNth_suffix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:09:55.215078+00:00
-- url     : https://prove2.me/submissions/88fc0e3d-17e0-45e1-ab78-1393bbba9c8e

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
theorem _root_.solution {m p q : ℕ} (op : α → α → α) (x : Fin (m + 1) → α) (j : Fin (m + 1))
    (j' : Fin (q + 1)) (hpq : p + q = m) (hj : (j : ℕ) = p + j') :
    (fun l : Fin q => Fin.contractNth j op x ⟨p + l, by omega⟩) =
      Fin.contractNth j' op (fun l : Fin (q + 1) => x ⟨p + l, by omega⟩) := by
  funext l
  simp only [Fin.contractNth, Fin.castSucc_mk, Fin.succ_mk, hj]
  by_cases h1 : (l : ℕ) < j'
  · rw [if_pos (by omega), if_pos h1]
    rfl
  · rw [if_neg (by omega), if_neg h1]
    by_cases h2 : (l : ℕ) = j'
    · rw [if_pos (by omega), if_pos h2]
      rfl
    · rw [if_neg (by omega), if_neg h2]
      rfl
end GroundTheory.GroupCoh
