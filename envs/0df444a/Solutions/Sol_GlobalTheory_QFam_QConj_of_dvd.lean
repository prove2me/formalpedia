-- Prove2me | solution 1 for GlobalTheory.QFam.QConj.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:41:29.29579+00:00
-- url     : https://prove2.me/submissions/12684fa3-21d2-4747-9ad1-4cdcad102f11

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
namespace QConj
theorem _root_.solution {N N' : ℕ} (h : 0 < N') (hd : N ∣ N') {g : ℂ ≃+* ℂ} {f f' : ℍ → ℂ}
    (hf : QConj g N f f') : QConj g N' f f' := by
  obtain ⟨M, rfl⟩ := hd
  have hN : 0 < N := Nat.pos_of_mul_pos_right h
  have hM : 0 < M := Nat.pos_of_mul_pos_left h
  obtain ⟨a, ha, ha'⟩ := hf
  refine ⟨spread M a, hasQ_mul_spread N M f a hN hM ha, ?_⟩
  have key : (fun n => g (spread M a n)) = spread M (fun n => g (a n)) := by
    funext n
    unfold spread
    split_ifs <;> simp
  rw [key]
  exact hasQ_mul_spread N M f' _ hN hM ha'
end QConj
end GlobalTheory.QFam
