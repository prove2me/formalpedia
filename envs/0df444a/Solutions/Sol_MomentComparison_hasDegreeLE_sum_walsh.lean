-- Prove2me | solution 1 for MomentComparison.hasDegreeLE_sum_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:19:28.38173+00:00
-- url     : https://prove2.me/submissions/63db9961-5d04-4ecf-b8c5-7a7590829683

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
theorem _root_.solution {n d : ℕ} {ι : Type*} (u : Finset ι)
    (s : ι → Finset (Fin n)) (a : ι → ℝ)
    (h : ∀ i ∈ u, (s i).card ≤ d) :
    HasDegreeLE (fun x => ∑ i ∈ u, a i * walsh (s i) x) d := by
  intro t ht
  change cubeAverage (fun x => (∑ i ∈ u, a i * walsh (s i) x) * walsh t x) = 0
  simp_rw [sum_mul, mul_assoc]
  rw [cubeAverage_sum]
  apply sum_eq_zero
  intro i hi
  have hne : s i ≠ t := fun he => (not_lt_of_ge (he ▸ h i hi)) ht
  simp [cubeAverage_const_mul, cubeAverage_walsh_mul, hne]
end MomentComparison
