-- Prove2me | solution 1 for GlobalTheory.T.hasQExpansionOfLevel_linear_operations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:15:41.844877+00:00
-- url     : https://prove2.me/submissions/a8374440-b84c-4a6d-8397-d3256be1b8e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperationsStatement
import Theorems.Thm_GlobalTheory_QFam_hasQ_linear


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ), (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ + g τ) (fun n => a n + b n)) ∧ (∀ f g a b, HasQ N f a → HasQ N g b → HasQ N (fun τ => f τ - g τ) (fun n => a n - b n)) ∧ (∀ (c : ℂ) f a, HasQ N f a → HasQ N (fun τ => c * f τ) (fun n => c * a n)) ∧ (∀ c : ℂ, HasQ N (fun _ => c) (fun n => if n = 0 then c else 0)) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ) (a : κ → ℕ → ℂ), (∀ k ∈ s, HasQ N (f k) (a k)) → HasQ N (fun τ => ∑ k ∈ s, f k τ) (fun n => ∑ k ∈ s, a k n)) := by
  first | exact @GlobalTheory.QFam.hasQ_linear | exact GlobalTheory.QFam.hasQ_linear | (intros; apply GlobalTheory.QFam.hasQ_linear <;> assumption)
end _root_.GlobalTheory.T
