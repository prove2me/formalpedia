-- Prove2me | solution 1 for GlobalTheory.FormalCalc.formalLog_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:43:43.458421+00:00
-- url     : https://prove2.me/submissions/cc9c4690-83cb-47c5-bfbf-92c4cccf7ef1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Theorems.Thm_GlobalTheory_FormalCalc_formalExp_zero
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_one
import Theorems.Thm_GlobalTheory_FormalCalc_formalLog_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FormalCalc.formalExp_zero
attribute [local simp] GlobalTheory.FormalCalc.formalLog_one

set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries
variable {σ τ A B : Type*} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
namespace GlobalTheory.FormalCalc
theorem _root_.solution {κ : Type*} (s : Finset κ) {g : κ → MvPowerSeries σ A}
    (hg : ∀ k ∈ s, constantCoeff (g k) = 1) :
    formalLog (∏ k ∈ s, g k) = ∑ k ∈ s, formalLog (g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have h' : ∀ j ∈ s, constantCoeff (g j) = 1 := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.prod_insert hk, formalLog_mul
      (hg k (Finset.mem_insert_self _ _)) (by rw [map_prod]; exact Finset.prod_eq_one h'), ih h']
end GlobalTheory.FormalCalc
