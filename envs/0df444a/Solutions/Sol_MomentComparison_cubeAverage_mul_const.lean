-- Prove2me | solution 1 for MomentComparison.cubeAverage_mul_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:04:24.228742+00:00
-- url     : https://prove2.me/submissions/72a98b0c-7cc1-4d35-8128-4188f84bc5d1

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
public import Theorems.Thm_MomentComparison_cubeAverage_const_mul
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (f : Cube n → ℝ) (c : ℝ) :
    cubeAverage (fun x => f x * c) = cubeAverage f * c := by
  simpa only [mul_comm] using cubeAverage_const_mul c f
end MomentComparison
