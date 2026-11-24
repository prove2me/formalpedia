-- Prove2me | solution 1 for MomentComparison.walshLayer_sq_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:07:27.776089+00:00
-- url     : https://prove2.me/submissions/70980131-ba2e-443d-a625-d3c7dd30b731

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_Walsh
public import Theorems.Thm_MomentComparison_walsh_symmDiff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators symmDiff
open MomentComparison
open Finset
namespace MomentComparison
theorem _root_.solution (n m : ℕ) (x : Cube n) :
    walshLayer n m x ^ 2 = ∑ T : Finset (Fin n), (walshPairCount n m T : ℝ) * walsh T x := by
  simp_rw [walshLayer, pow_two, sum_mul, mul_sum, ← walsh_symmDiff, ← sum_product']
  let u := (univ : Finset (Fin n)).powersetCard m
  rw [← sum_fiberwise (u ×ˢ u) (fun st => st.1 ∆ st.2) (fun st => walsh (st.1 ∆ st.2) x)]
  apply sum_congr rfl
  intro T _
  unfold walshPairCount
  rw [← nsmul_eq_mul, ← sum_const]
  exact sum_congr rfl (fun st hst => congrArg (fun S => walsh S x) (mem_filter.mp hst).2)
end MomentComparison
