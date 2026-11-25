-- Prove2me | solution 1 for HiltonMilner.shiftSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:09:28.003199+00:00
-- url     : https://prove2.me/submissions/68ca58ce-c76d-4d8a-b4ef-db1be5c1ebdc

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift

set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner
namespace HiltonMilner
theorem _root_.solution {y z : ℕ} {X A : Finset ℕ} (hy : y ∈ X) (hA : A ⊆ X) :
    shiftSet y z A ⊆ X := by
  unfold shiftSet
  split_ifs
  · exact insert_subset hy ((erase_subset _ _).trans hA)
  · exact hA
end HiltonMilner
