-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:46.841511+00:00
-- url     : https://prove2.me/submissions/db843fdb-3237-471f-ad49-eabcfa968db2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_map_conv
import Theorems.Thm_GlobalTheory_QFam_HasQ_mul_conv__e97469


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
theorem _root_.solution (hN : 0 < N) {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ := by
  obtain ⟨a, ha, ha'⟩ := hf
  obtain ⟨b, hb, hb'⟩ := hh
  refine ⟨conv a b, ha.mul_conv hb, ?_⟩
  have e : (fun n => g (conv a b n)) = conv (fun n => g (a n)) (fun n => g (b n)) :=
    funext (map_conv g a b)
  rw [e]
  exact ha'.mul_conv hb'
end QConj
end GlobalTheory.QFam
