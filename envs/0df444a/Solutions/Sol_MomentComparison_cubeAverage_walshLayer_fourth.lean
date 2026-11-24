-- Prove2me | solution 1 for MomentComparison.cubeAverage_walshLayer_fourth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:15.9148+00:00
-- url     : https://prove2.me/submissions/7a3520a9-247b-4f4d-96b0-ea62c9b647ee

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
public import Theorems.Thm_MomentComparison_cubeAverage_const_mul
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_cubeAverage_walsh_mul
public import Theorems.Thm_MomentComparison_walshLayer_sq_expansion
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
    cubeAverage (fun x => walshLayer n m x ^ 4) =
      ∑ T : Finset (Fin n), (walshPairCount n m T : ℝ) ^ 2 := by
  have hpow (z : ℝ) : z ^ 4 = z ^ 2 * z ^ 2 := by ring
  simp_rw [hpow, walshLayer_sq_expansion, sum_mul, mul_sum, cubeAverage_sum]
  let a := fun T : Finset (Fin n) => (walshPairCount n m T : ℝ)
  change (∑ s : Finset (Fin n), ∑ t : Finset (Fin n),
    cubeAverage (fun x => (a s * walsh s x) * (a t * walsh t x))) = _
  have havg (s t : Finset (Fin n)) :
      cubeAverage (fun x => (a s * walsh s x) * (a t * walsh t x)) =
      if s = t then (a s)^2 else 0 := by
    have ha (x : Cube n) : (a s * walsh s x) * (a t * walsh t x) =
        (a s * a t) * (walsh s x * walsh t x) := by ring
    simp_rw [ha, cubeAverage_const_mul, cubeAverage_walsh_mul]
    split_ifs with h
    · subst t
      simp [pow_two]
    · simp
  simp_rw [havg]
  simp [a]
end MomentComparison
