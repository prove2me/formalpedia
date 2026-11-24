-- Prove2me | solution 1 for MomentComparison.cubeAverage_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:24:09.096897+00:00
-- url     : https://prove2.me/submissions/6ae8b11d-479c-47da-be90-63fa751e4b3a

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
public import Theorems.Thm_MomentComparison_cubeSign_mul_self
public import Theorems.Thm_MomentComparison_cubeAverage_const
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self
attribute [local simp] MomentComparison.cubeAverage_const

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (f : Cube (n + 1) → ℝ) :
    cubeAverage f = (cubeAverage (fun x => f (Fin.cons true x)) +
      cubeAverage (fun x => f (Fin.cons false x))) / 2 := by
  unfold cubeAverage
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun x => rfl)]
  rw [Fintype.sum_prod_type]
  have h : (Finset.univ : Finset Bool) = {true, false} := by decide
  rw [h]
  simp [pow_succ]
  ring
end MomentComparison
