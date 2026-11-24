-- Prove2me | solution 1 for GlobalTheory.T.bertini_general_members_no_derivative_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:07:27.92574+00:00
-- url     : https://prove2.me/submissions/21d0d18b-30d6-4959-8f90-b6a4a7300c55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
import Theorems.Thm_GlobalTheory_BertiniC_no_dependence_of_general


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) (δ : Fin n → Derivation k A A) (ω : Fin n → KaehlerDifferential k A), (∀ a : A, KaehlerDifferential.D k A a = ∑ l, δ l a • ω l) → ∀ {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ) (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι), i₀ ∈ J → ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (K : Type) [Field K] [Algebra k K] (φ : A →ₐ[k] K) (c : Fin M → K), φ (f p₀) ≠ 0 → c i₀ = 1 → (∀ i ∈ J, φ (∑ p, u (i, p) • f p) = 0) → ¬ ∀ l, ∑ i ∈ J, c i * φ (δ l (∑ p, u (i, p) • f p)) = 0 := by
  first | exact @GlobalTheory.BertiniC.no_dependence_of_general | exact GlobalTheory.BertiniC.no_dependence_of_general | (intros; apply GlobalTheory.BertiniC.no_dependence_of_general <;> assumption)
end _root_.GlobalTheory.T
