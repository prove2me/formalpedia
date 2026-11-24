-- Prove2me | solution 1 for GlobalTheory.MvPoly.multiFactorial_add_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:02:35.631897+00:00
-- url     : https://prove2.me/submissions/8147d0cc-783d-4b53-9f84-6ac567af4dee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SumFinsuppAntidiagProdPowDivMultiFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open GlobalTheory GlobalTheory.MvPoly
variable {σ τ K L : Type*}
namespace GlobalTheory.MvPoly
theorem _root_.solution (α : σ →₀ ℕ) (i : σ) :
    multiFactorial (α + Finsupp.single i 1) = (α i + 1) * multiFactorial α := by
  classical
  have h1 : ∀ β : σ →₀ ℕ, β.support ⊆ insert i α.support →
      multiFactorial β = (β i).factorial * ∏ j ∈ (insert i α.support).erase i, (β j).factorial :=
    fun β hβ ↦ by
      rw [multiFactorial, Finsupp.prod_of_support_subset β hβ _ fun _ _ ↦ rfl,
        mul_prod_erase _ (fun j ↦ (β j).factorial) (mem_insert_self _ _)]
  rw [h1 α (subset_insert _ _), h1 _ (Finsupp.support_add.trans ?_), ← mul_assoc]
  · congr 1
    · simp [Nat.factorial_succ]
    · refine prod_congr rfl fun j hj ↦ ?_
      simp [Finsupp.single_eq_of_ne (ne_of_mem_erase hj)]
  · exact union_subset (subset_insert _ _)
      (Finsupp.support_single_subset.trans (by simp))
end GlobalTheory.MvPoly
