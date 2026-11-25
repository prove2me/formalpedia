-- Prove2me | solution 1 for NashWilliams.cutF_inter_add_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:15:48.510281+00:00
-- url     : https://prove2.me/submissions/bed8f6a6-e63b-42ab-a713-22e367b57cd5

module
public import Mathlib
public import Definitions.Def_NashWilliamsLib_Basic
public import Theorems.Thm_NashWilliams_cutF_eq_sum

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    cutF ends F (X ∩ Y) + cutF ends F (X ∪ Y) ≤ cutF ends F X + cutF ends F Y := by
  simp only [cutF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  unfold cr
  by_cases h1 : (ends i).1 ∈ X <;> by_cases h2 : (ends i).1 ∈ Y <;>
    by_cases h3 : (ends i).2 ∈ X <;> by_cases h4 : (ends i).2 ∈ Y <;> simp [*]
end NashWilliams
