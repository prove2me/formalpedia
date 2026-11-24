-- Prove2me | solution 1 for MomentComparison.cubeAverage_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:18:52.006939+00:00
-- url     : https://prove2.me/submissions/f402f00b-bb8a-47c1-8038-052e003c8206

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
theorem _root_.solution {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Cube n → ℝ) :
    cubeAverage (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAverage (f i) := by
  simp only [cubeAverage, div_eq_mul_inv, ← sum_mul]
  congr 1
  exact sum_comm
end MomentComparison
