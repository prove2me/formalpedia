-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:17:53.095885+00:00
-- url     : https://prove2.me/submissions/cb4286bb-a3d6-47a6-bb58-c225381b26fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_QConj_const
import Theorems.Thm_GlobalTheory_QFam_QConj_mul
import Theorems.Thm_GlobalTheory_QFam_HasQ_const


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
variable {g : ℂ ≃+* ℂ} {N : ℕ}
namespace GlobalTheory.QFam
namespace QConj
theorem _root_.solution (hN : 0 < N) {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.prod_empty]
    simpa using QConj.const g N 1
  · intro j s hj ih h
    simp only [Finset.prod_insert hj]
    exact QConj.mul hN (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
end QConj
end GlobalTheory.QFam
