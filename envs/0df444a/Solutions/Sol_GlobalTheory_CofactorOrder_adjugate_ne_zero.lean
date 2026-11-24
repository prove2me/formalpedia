-- Prove2me | solution 1 for GlobalTheory.CofactorOrder.adjugate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:14:34.131541+00:00
-- url     : https://prove2.me/submissions/693cb019-6eab-4511-806c-527e3043cc52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Theorems.Thm_GlobalTheory_CofactorOrder_exists_diag
import Theorems.Thm_GlobalTheory_CofactorOrder_card_le_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix
open GlobalTheory
open GlobalTheory.CofactorOrder
variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
namespace GlobalTheory.CofactorOrder
theorem _root_.solution [Nonempty n] (M : Matrix n n K)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) ≤ 1) : M.adjugate ≠ 0 := by
  classical
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag M
  have hone := Fintype.card_le_one_iff.mp ((card_le_finrank hP hQ hPQ).trans h)
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, j ≠ i → D j ≠ 0 := by
    by_cases hex : ∃ i, D i = 0
    · obtain ⟨i, hi0⟩ := hex
      exact ⟨i, fun j hj hj0 => hj (congrArg Subtype.val (hone ⟨j, hj0⟩ ⟨i, hi0⟩))⟩
    · push Not at hex
      exact ⟨Classical.arbitrary n, fun j _ => hex j⟩
  intro hM
  have hdiag : (diagonal D).adjugate = 0 := by
    rw [← hPQ, adjugate_mul_distrib, adjugate_mul_distrib, hM, Matrix.zero_mul, Matrix.mul_zero]
  have hii := congrFun (congrFun hdiag i) i
  rw [adjugate_diagonal, diagonal_apply_eq, Matrix.zero_apply] at hii
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => hi j (Finset.ne_of_mem_erase hj)) hii
end GlobalTheory.CofactorOrder
