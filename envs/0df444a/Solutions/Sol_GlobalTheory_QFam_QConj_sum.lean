-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.794308+00:00
-- url     : https://prove2.me/submissions/146730e3-a131-4a81-b5ef-c127f101e43c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_QConj_const
import Theorems.Thm_GlobalTheory_QFam_QConj_add
import Theorems.Thm_GlobalTheory_QFam_HasQ_add
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
theorem _root_.solution {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    simpa using QConj.const g N 0
  · intro j s hj ih h
    simp only [Finset.sum_insert hj]
    exact QConj.add (h j (Finset.mem_insert_self j s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
end QConj
end GlobalTheory.QFam
