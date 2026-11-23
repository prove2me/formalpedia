-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:45.8498+00:00
-- url     : https://prove2.me/submissions/9470bc89-c3b2-43e0-b1ab-0420bc37b9a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
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
theorem _root_.solution (g : ℂ ≃+* ℂ) (N : ℕ) (c : ℂ) : QConj g N (fun _ => c) fun _ => g c := by
  refine ⟨fun n => if n = 0 then c else 0, HasQ.const N c, ?_⟩
  have e : (fun n : ℕ => g (if n = 0 then c else 0)) = fun n => if n = 0 then g c else 0 := by
    funext n
    split_ifs <;> simp
  rw [e]
  exact HasQ.const N (g c)
end QConj
end GlobalTheory.QFam
