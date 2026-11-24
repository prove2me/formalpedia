-- Prove2me | solution 1 for MomentComparison.walshExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:12:52.889891+00:00
-- url     : https://prove2.me/submissions/f1ca9b17-132a-4a6b-93cc-af634983e184

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
public import Theorems.Thm_MomentComparison_cubeAverage_sum
public import Theorems.Thm_MomentComparison_cubeAverage_mul_const
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_walsh_kernel
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
theorem _root_.solution {n : ℕ} (f : Cube n → ℝ) (x : Cube n) :
    (∑ s : Finset (Fin n), (cubeAverage fun y => f y * walsh s y) * walsh s x) = f x := by
  calc
    _ = (∑ s : Finset (Fin n), cubeAverage (fun y => f y * (walsh s y * walsh s x))) := by
      simp_rw [← mul_assoc, cubeAverage_mul_const]
    _ = cubeAverage (fun y => f y * ∑ s : Finset (Fin n), walsh s y * walsh s x) := by
      simp_rw [mul_sum, cubeAverage_sum]
    _ = f x := by
      simp only [walsh_kernel, mul_ite, mul_zero, cubeAverage, Fintype.sum_ite_eq',
        mul_div_cancel_right₀ _ (show (2 : ℝ)^n ≠ 0 by positivity)]
end MomentComparison
