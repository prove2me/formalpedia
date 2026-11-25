-- Prove2me | solution 1 for NashWilliams.cutF_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:17:41.205161+00:00
-- url     : https://prove2.me/submissions/1dafc47a-1ce1-4e1a-9a37-c6d1ca30644e

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
theorem _root_.solution {ends : ι → V × V} {F : Finset ι} {X : Finset V} {x y : V} (hxy : x ≠ y)
    (hx : x ∈ X) (hy : y ∈ X) (hno : ∀ i ∈ F, ¬ ((ends i).1 ∈ X ∧ (ends i).2 ∈ X)) :
    cutF ends F {x} + cutF ends F {y} ≤ cutF ends F X := by
  simp only [cutF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have := hno i hi
  unfold cr
  by_cases h1 : (ends i).1 ∈ X <;> by_cases h2 : (ends i).2 ∈ X <;>
    by_cases h3 : (ends i).1 = x <;> by_cases h4 : (ends i).2 = x <;>
    by_cases h5 : (ends i).1 = y <;> by_cases h6 : (ends i).2 = y <;> simp_all
end NashWilliams
