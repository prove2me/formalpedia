-- Prove2me | solution 1 for GlobalTheory.QFam.QAll.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:41:31.421823+00:00
-- url     : https://prove2.me/submissions/9d991f34-cd80-451a-8584-345ebe2abe33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulLevelSubstPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QAllQConjOfDvd
import Theorems.Thm_GlobalTheory_QFam_hasQ_mul_spread


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam
namespace GlobalTheory.QFam
namespace QAll
theorem _root_.solution {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {p : ℂ → Prop} {f : ℍ → ℂ}
    (h0 : p 0) (hf : QAll p N f) : QAll p N' f := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, hpa⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, fun n => ?_⟩
  unfold spread
  split_ifs
  · exact hpa _
  · exact h0
end QAll
end GlobalTheory.QFam
