-- Prove2me | solution 1 for NashWilliams.total_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:46:22.944228+00:00
-- url     : https://prove2.me/submissions/72f0af6a-7536-48b7-ad6c-74b95fdaa34b

module
public import Mathlib
public import Definitions.Def_TreePackingLib_NashWilliamsAux

set_option autoImplicit true
@[expose] public section
public section
open Finset Fintype SimpleGraph Function
open NashWilliams
variable {V : Type*}
variable (G : SimpleGraph V) {k : ℕ}
variable {G}
namespace NashWilliams
theorem _root_.solution (F : Fin k → SimpleGraph V) (i : Fin k) (X : SimpleGraph V) :
    total (update F i X) + (F i).edgeSet.ncard = total F + X.edgeSet.ncard := by
  simp only [total]
  rw [show (fun j ↦ (update F i X j).edgeSet.ncard) =
      update (fun j ↦ (F j).edgeSet.ncard) i X.edgeSet.ncard from
    funext fun j ↦ apply_update (fun _ (H : SimpleGraph V) ↦ H.edgeSet.ncard) F i X j]
  rw [Finset.sum_update_of_mem (mem_univ i), Finset.sdiff_singleton_eq_erase]
  have := Finset.add_sum_erase univ (fun j ↦ (F j).edgeSet.ncard) (mem_univ i)
  omega
end NashWilliams
