-- Prove2me | solution 1 for NashWilliams.cutF_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:01:38.54157+00:00
-- url     : https://prove2.me/submissions/96e0bc05-413a-412a-ae10-6299dd6e96fc

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
public import Theorems.Thm_NashWilliams_sum_split
public import Theorems.Thm_NashWilliams_cutF_eq_sum


set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution [DecidableEq ι] {ends : ι → V × V} {F : Finset ι} {i j : ι} (hi : i ∈ F)
    (hj : j ∈ F) (hij : i ≠ j) (u v : V) (S : Finset V) :
    cutF ends F S + cr (u, v) S =
      cutF (Function.update ends i (u, v)) (F.erase j) S + cr (ends i) S + cr (ends j) S := by
  rw [cutF_eq_sum, cutF_eq_sum]
  have := sum_split (f := fun l => cr (ends l) S)
    (f1 := fun l => cr (Function.update ends i (u, v) l) S) hi hj hij
    (fun l _ hli _ => by simp [Function.update_of_ne hli])
  simpa using this
end NashWilliams
