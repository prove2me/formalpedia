-- Prove2me | solution 1 for GlobalTheory.QFam.qConj_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:41:08.509809+00:00
-- url     : https://prove2.me/submissions/d7354025-cf52-4b12-8268-7b0fd7ce7085

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_QConj_const
import Theorems.Thm_GlobalTheory_QFam_QConj_add
import Theorems.Thm_GlobalTheory_QFam_QConj_sub
import Theorems.Thm_GlobalTheory_QFam_QConj_mul
import Theorems.Thm_GlobalTheory_QFam_QConj_pow
import Theorems.Thm_GlobalTheory_QFam_QConj_sum
import Theorems.Thm_GlobalTheory_QFam_QConj_prod
import Theorems.Thm_GlobalTheory_QFam_HasQ_add
import Theorems.Thm_GlobalTheory_QFam_HasQ_const
import Theorems.Thm_GlobalTheory_QFam_HasQ_sub
import Theorems.Thm_GlobalTheory_QFam_HasQ_sum


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
theorem _root_.solution : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  intro g N hN
  exact ⟨fun c => QConj.const g N c,
    fun _ _ _ _ hf hh => QConj.add hf hh,
    fun _ _ _ _ hf hh => QConj.sub hf hh,
    fun _ _ _ _ hf hh => QConj.mul hN hf hh,
    fun _ _ k hf => QConj.pow hN k hf,
    fun _ s _ _ h => ⟨QConj.sum s h, QConj.prod hN s h⟩⟩
end GlobalTheory.QFam
