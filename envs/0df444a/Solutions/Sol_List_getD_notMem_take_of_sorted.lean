-- Prove2me | solution 1 for List.getD_notMem_take_of_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:15.491229+00:00
-- url     : https://prove2.me/submissions/5c40cae9-cbd0-4f4f-93c2-a926bbcc3e0a

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List

set_option autoImplicit false
public section
open List
variable {α β : Type*}
variable [LinearOrder α]
namespace List
theorem _root_.solution {l : List α} (hs : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length)
    (d : α) (h : i = 0 ∨ l.getD i d ≠ l.getD (i - 1) d) : l.getD i d ∉ l.take i := by
  intro hm
  obtain ⟨j, hj, hsame⟩ := List.mem_iff_getElem.1 hm
  have hji : j < i := (List.length_take_le i l).trans_lt' hj
  rcases h with rfl | hne
  · omega
  rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (show i - 1 < l.length by omega)] at hne
  rw [List.getElem_take, List.getD_eq_getElem _ _ hi] at hsame
  have hpred : l[i - 1] ≤ l[i] := List.pairwise_iff_getElem.1 hs _ _ _ _ (by omega)
  have hle : l[j] ≤ l[i - 1] := by
    rcases Nat.lt_or_ge j (i - 1) with hlt | hge
    · exact List.pairwise_iff_getElem.1 hs _ _ _ _ hlt
    · exact le_of_eq (by congr 1; omega)
  -- `l[j] ≤ l[i - 1] ≤ l[i] = l[j]`, so `l[i - 1] = l[i]`
  exact hne (le_antisymm (hsame ▸ hle) hpred)
end List
