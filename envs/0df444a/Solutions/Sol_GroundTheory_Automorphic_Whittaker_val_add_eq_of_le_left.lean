-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.val_add_eq_of_le_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:29.278735+00:00
-- url     : https://prove2.me/submissions/38e859b5-87cb-481c-aedb-5f017507527a

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
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by
  set L := univ.filter fun y : Fin n => y < b ∧ w y < w b with hL
  by_cases hne : L.Nonempty
  · set m := L.min' hne
    have hm : m ∈ L := L.min'_mem hne
    rw [hL, mem_filter] at hm
    have hsub : L ⊆ Ico m b := by
      intro y hy
      have hy' := hy
      rw [hL, mem_filter] at hy'
      exact mem_Ico.2 ⟨L.min'_le y hy, hy'.2.1⟩
    have hcard : #L ≤ b.val - m.val := by
      have := card_le_card hsub
      rwa [Fin.card_Ico] at this
    have hmb := Fin.lt_def.1 hm.2.1
    have hwmb := Fin.lt_def.1 hm.2.2
    have h1 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) x
      (Fin.le_iff_val_le_val.2 (by omega)) hxb
    have h2 := val_eq_of_le_of_le hB ((w b).val - (w m).val) m b (by omega) (le_of_lt hm.2.1) b
      (le_of_lt hm.2.1) le_rfl
    rw [Fin.le_iff_val_le_val] at hxb
    omega
  · rw [not_nonempty_iff_eq_empty] at hne
    rw [hne, card_empty] at hx
    have : x = b := Fin.ext (by rw [Fin.le_iff_val_le_val] at hxb; omega)
    subst this
    simp
end GroundTheory.Automorphic.Whittaker
