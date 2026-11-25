-- Prove2me | solution 1 for NashWilliams.dsF_union_add_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:22:15.990409+00:00
-- url     : https://prove2.me/submissions/d76afdd9-41ff-4ca1-a45d-22e62ddd69ef

module
public import Definitions.Def_NashWilliamsLib_Basic
public import Definitions.Def_NashWilliamsLib_Splitting
public import Theorems.Thm_NashWilliams_dsF_eq_sum

set_option autoImplicit true
@[expose] public section
public section
open Finset
open NashWilliams
variable {V ι : Type*} [DecidableEq V]
namespace NashWilliams
theorem _root_.solution (s : V) (ends : ι → V × V) (F : Finset ι) (X Y : Finset V) :
    dsF s ends F X + dsF s ends F Y = dsF s ends F (X ∪ Y) + dsF s ends F (X ∩ Y) := by
  simp only [dsF_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold jn
  by_cases a1 : (ends l).1 = s <;> by_cases a2 : (ends l).2 = s <;>
    by_cases b1 : (ends l).1 ∈ X <;> by_cases b2 : (ends l).2 ∈ X <;>
    by_cases c1 : (ends l).1 ∈ Y <;> by_cases c2 : (ends l).2 ∈ Y <;> simp_all
end NashWilliams
