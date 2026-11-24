-- Prove2me | solution 1 for GlobalTheory.QFam.hasQ_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:31.422566+00:00
-- url     : https://prove2.me/submissions/fa676298-fffc-4fba-8448-48a9794fd730

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Theorems.Thm_GlobalTheory_QFam_HasQ_add
import Theorems.Thm_GlobalTheory_QFam_HasQ_sub
import Theorems.Thm_GlobalTheory_QFam_HasQ_const_mul
import Theorems.Thm_GlobalTheory_QFam_HasQ_const
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
namespace GlobalTheory.QFam
theorem _root_.solution : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  intro N
  exact ⟨fun f g a b hf hg => hf.add hg, fun f g a b hf hg => hf.sub hg,
    fun c f a hf => hf.const_mul c, fun c => HasQ.const N c, fun κ s f a h => HasQ.sum s h⟩
end GlobalTheory.QFam
