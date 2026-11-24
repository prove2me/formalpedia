-- Prove2me | solution 1 for MomentComparison.cubeAverage_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:21:05.685778+00:00
-- url     : https://prove2.me/submissions/4be5e49c-7395-46f5-8193-5b1045005840

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
attribute [local simp] MomentComparison.walsh_empty
attribute [local simp] MomentComparison.cubeSign_mul_self

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution {n : ℕ} (c : ℝ) (f : Cube n → ℝ) :
    cubeAverage (fun x => c * f x) = c * cubeAverage f := by
  simp only [cubeAverage, ← mul_sum, mul_div_assoc]
end MomentComparison
