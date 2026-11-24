-- Prove2me | solution 1 for MomentComparison.cubeAverage_walshLayer_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:21:38.436905+00:00
-- url     : https://prove2.me/submissions/c34bfaa4-8a79-4ffe-b59b-1a0fb8f1ad4d

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
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_walsh_mul
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
theorem _root_.solution (n m : ℕ) :
    cubeAverage (fun x => walshLayer n m x ^ 2) = (n.choose m : ℝ) := by
  simp_rw [walshLayer, pow_two, sum_mul, mul_sum, cubeAverage_sum, cubeAverage_walsh_mul]
  have h : ((univ : Finset (Fin n)).powersetCard m).filter (fun s => s.card = m) =
      (univ : Finset (Fin n)).powersetCard m :=
    filter_true_of_mem fun _ hs => (mem_powersetCard.mp hs).2
  simp [h, card_powersetCard]
end MomentComparison
