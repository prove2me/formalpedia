-- Prove2me | solution 1 for MomentComparison.cubeSign_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:14:52.272671+00:00
-- url     : https://prove2.me/submissions/fef64a03-630c-45fa-9034-78a91780d8c2

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_empty
attribute [local simp] MomentComparison.walsh_empty

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeSign x i * cubeSign x i = 1 := by
  cases h : x i <;> simp [cubeSign, h]
end MomentComparison
