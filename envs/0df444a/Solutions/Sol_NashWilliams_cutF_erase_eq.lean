-- Prove2me | solution 1 for NashWilliams.cutF_erase_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:16:39.736882+00:00
-- url     : https://prove2.me/submissions/2cc02115-2146-41b7-b9e2-6d927d3133e4

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution (ends : ι → V × V) (F : Finset ι) (S : Finset V) [DecidableEq ι] (i : ι)
    (h : ¬ (((ends i).1 ∈ S) ≠ ((ends i).2 ∈ S))) :
    cutF ends (F.erase i) S = cutF ends F S := by
  unfold cutF
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ => h
end NashWilliams
