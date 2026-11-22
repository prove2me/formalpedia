-- Prove2me | solution 1 for LatinQuarter.fillingOrder_column
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:21:41.011453+00:00
-- url     : https://prove2.me/submissions/02e53da2-15c4-4c11-8063-aca0b52977d4

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
theorem _root_.solution {n : ℕ} (r c j : Fin n) (hj : c < j) :
    fillingOrder r j < fillingOrder r c := by
  have hc := c.isLt
  have hjn := j.isLt
  unfold fillingOrder
  omega
end LatinQuarter
