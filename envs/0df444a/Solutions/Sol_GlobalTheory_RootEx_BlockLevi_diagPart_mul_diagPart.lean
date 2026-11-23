-- Prove2me | solution 1 for GlobalTheory.RootEx.BlockLevi.diagPart_mul_diagPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:59.673372+00:00
-- url     : https://prove2.me/submissions/f5a90533-a8db-4661-b1df-e1099911801d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart
import Theorems.Thm_GlobalTheory_RootEx_BlockLevi_mul_diagPart_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.BlockLevi
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.BlockLevi
theorem _root_.solution (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) (hAB : A * B = 1) :
    diagPart f A * diagPart f B = 1 := by
  ext r s
  by_cases h : f r = f s
  · rw [← hAB, ← mul_diagPart_apply f hA hB h.ge]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_pos (h.trans ht.symm)]
    · simp [ht]
  · have hrs : r ≠ s := fun e => h (e ▸ rfl)
    rw [Matrix.one_apply_ne hrs]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_neg (fun e => h (e.trans ht))]; simp
    · simp [ht]
end GlobalTheory.RootEx.BlockLevi
