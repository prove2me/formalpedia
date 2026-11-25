-- Prove2me | solution 1 for GroundTheory.GroupCoh.partialProd_contractNth_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:10:43.583596+00:00
-- url     : https://prove2.me/submissions/edf480f8-7608-4ef7-818e-6003b968859f

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
namespace GroundTheory.GroupCoh
theorem _root_.solution {m p : ℕ} (x : Fin (m + 1) → M) (j : Fin (m + 1))
    (hp : p ≤ m) (hj : (j : ℕ) < p) :
    Fin.partialProd (Fin.contractNth j (· * ·) x) ⟨p, by omega⟩ =
      Fin.partialProd x ⟨p + 1, by omega⟩ := by
  rw [Fin.partialProd_contractNth]
  simp only [Function.comp_apply]
  congr 1
  rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · simp [Fin.le_def]; omega
end GroundTheory.GroupCoh
