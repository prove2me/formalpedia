-- Prove2me | solution 1 for GroundTheory.GroupCoh.partialProd_prefix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:48:42.381811+00:00
-- url     : https://prove2.me/submissions/a7aa0691-a6cc-4f44-834c-1773d3b0be9b

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
variable {A B : Rep k G} {p q n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution {M : Type*} [Monoid M] {m m' j : ℕ} (x : Fin m' → M) (hm : m ≤ m')
    (hj : j ≤ m) :
    Fin.partialProd (fun i : Fin m => x ⟨i, by omega⟩) ⟨j, by omega⟩ =
      Fin.partialProd x ⟨j, by omega⟩ := by
  induction j with
  | zero => simp [Fin.partialProd]
  | succ j ih =>
    have h1 := Fin.partialProd_succ x ⟨j, by omega⟩
    have h2 := Fin.partialProd_succ (fun i : Fin m => x ⟨i, by omega⟩) ⟨j, by omega⟩
    simp only [Fin.succ_mk, Fin.castSucc_mk] at h1 h2
    rw [h1, h2, ih (by omega)]
end GroundTheory.GroupCoh
