-- Prove2me | solution 1 for GlobalTheory.T.shuffle_count_linearIndependent_classes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:48.127398+00:00
-- url     : https://prove2.me/submissions/fe9653ca-2444-4ac5-a7f9-381abde228a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ShuffleCountLinearIndependentClasses
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ShuffleCountLinearIndependentClassesStatement
import Theorems.Thm_GlobalTheory_ShuffleCount_separates_of_shuffle_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I S : Type 1) (A : Type) [DecidableEq A] [LinearOrder A] (Ψ : (I →₀ ℤ) ≃+ MvPolynomial S ℤ) (M : I → List A → ℕ∞) (U : Set S) (ℓ : S → List A) (φ : S → ShuffleAlgebra ℚ A), Set.InjOn ℓ U → (∀ Δ ∈ U, IsLyndon (ℓ Δ) ∧ φ Δ = ShuffleAlgebra.word ℚ (ℓ Δ)) → (∀ Δ ∉ U, φ Δ = 0) → (∀ m : S →₀ ℕ, 0 ≤ Ψ.symm (MvPolynomial.monomial m 1) ∧ ∃ s : Multiset (List A), (∀ w, ((Ψ.symm (MvPolynomial.monomial m 1)).sum fun x a => (a.toNat : ℕ∞) * M x w) = (s.count w : ℕ∞)) ∧ (s.map (ShuffleAlgebra.word ℚ)).sum = m.prod fun Δ e => φ Δ ^ e) → ∀ (n : ℕ) (p : Fin n → I) (c : Fin n → ℂ), Function.Injective p → (∀ i, ∃ w, M (p i) w ≠ 0) → (∀ w, ∑ i, c i * ((M (p i) w).toNat : ℂ) = 0) → ∀ i, c i = 0 := by
  first | exact @GlobalTheory.ShuffleCount.separates_of_shuffle_count | exact GlobalTheory.ShuffleCount.separates_of_shuffle_count | (intros; apply GlobalTheory.ShuffleCount.separates_of_shuffle_count <;> assumption)
end _root_.GlobalTheory.T
