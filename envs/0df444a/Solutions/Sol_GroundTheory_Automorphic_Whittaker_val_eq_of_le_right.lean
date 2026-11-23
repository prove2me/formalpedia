-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.val_eq_of_le_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.223316+00:00
-- url     : https://prove2.me/submissions/398ec92d-786f-45db-ad73-3d1a4d7fbebb

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_eq_of_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by
  set R := univ.filter fun y : Fin n => b < y ∧ w b < w y with hR
  by_cases hne : R.Nonempty
  · set m := R.max' hne
    have hm : m ∈ R := R.max'_mem hne
    rw [hR, mem_filter] at hm
    have hsub : R ⊆ Ioc b m := by
      intro y hy
      have hy' := hy
      rw [hR, mem_filter] at hy'
      exact mem_Ioc.2 ⟨hy'.2.1, R.le_max' y hy⟩
    have hcard : #R ≤ m.val - b.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ioc] at this
    have hbm := Fin.lt_def.1 hm.2.1
    have hwbm := Fin.lt_def.1 hm.2.2
    exact val_eq_of_le_of_le hB ((w m).val - (w b).val) b m (by omega) (le_of_lt hm.2.1) x hbx
      (Fin.le_iff_val_le_val.2 (by omega))
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hbx; omega)
    subst this
    simp
end GroundTheory.Automorphic.Whittaker
