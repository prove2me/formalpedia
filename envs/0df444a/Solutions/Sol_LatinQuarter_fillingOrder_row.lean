-- Prove2me | solution 1 for LatinQuarter.fillingOrder_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:38.146611+00:00
-- url     : https://prove2.me/submissions/c3ab2955-a8e6-4924-b3b6-3f5b0a0975c2

module
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_LatinQuarter_Basic
public import Definitions.Def_LeanPool_LatinQuarter_Cyclic

set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter
namespace LatinQuarter
theorem _root_.solution {n : ℕ} (r i c d : Fin n) (hi : i < r) :
    fillingOrder i d < fillingOrder r c := by
  have hn := c.isLt
  have hd := d.isLt
  have hi' : i.val + 1 ≤ r.val := hi
  have hm := Nat.mul_le_mul_right n hi'
  have hrem : n - 1 - d.val < n := by omega
  unfold fillingOrder
  nlinarith
end LatinQuarter
