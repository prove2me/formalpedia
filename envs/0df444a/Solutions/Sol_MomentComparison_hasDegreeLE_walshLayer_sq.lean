-- Prove2me | solution 1 for MomentComparison.hasDegreeLE_walshLayer_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:22:34.139534+00:00
-- url     : https://prove2.me/submissions/da82ec9d-67d2-4aa3-9306-4c93fc86f2ca

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
public import Theorems.Thm_MomentComparison_walsh_symmDiff
public import Theorems.Thm_MomentComparison_cubeAverage_const
public import Theorems.Thm_MomentComparison_hasDegreeLE_sum_walsh
public import Theorems.Thm_MomentComparison_card_walsh_symmDiff_le
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
    HasDegreeLE (fun x => walshLayer n m x ^ 2) (2 * m) := by
  simp_rw [walshLayer, pow_two, sum_mul, mul_sum, ← walsh_symmDiff, ← sum_product']
  let u := (univ : Finset (Fin n)).powersetCard m
  simpa only [one_mul] using
    hasDegreeLE_sum_walsh (d := 2 * m) (u ×ˢ u) (fun st => st.1 ∆ st.2) (fun _ => 1) (by
      intro st hst
      obtain ⟨hs, ht⟩ := mem_product.mp hst
      calc
        _ ≤ st.1.card + st.2.card := card_walsh_symmDiff_le _ _
        _ = 2 * m := by rw [(mem_powersetCard.mp hs).2, (mem_powersetCard.mp ht).2, two_mul])
end MomentComparison
