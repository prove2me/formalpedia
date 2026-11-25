-- Prove2me | solution 1 for GlobalTheory.T.finite_of_bounded_embeddings_and_valuations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:16.863836+00:00
-- url     : https://prove2.me/submissions/7298ee93-26c2-4f2d-8121-d013ad5e7711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuations
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteOfBoundedEmbeddingsAndValuationsStatement
import Theorems.Thm_GlobalTheory_BddFinite_finite_of_bdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Filter
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (A : Set K) (R : ℝ), (∀ x ∈ A, ∀ τ : K →+* ℂ, ‖τ x‖ ≤ R) → (∀ w : HeightOneSpectrum (𝓞 K), ∃ B : WithZero (Multiplicative ℤ), ∀ x ∈ A, w.valuation K x ≤ B) → (∀ᶠ w : HeightOneSpectrum (𝓞 K) in cofinite, ∀ x ∈ A, w.valuation K x ≤ 1) → A.Finite := by
  first | exact @GlobalTheory.BddFinite.finite_of_bdd | exact GlobalTheory.BddFinite.finite_of_bdd | (intros; apply GlobalTheory.BddFinite.finite_of_bdd <;> assumption)
end _root_.GlobalTheory.T
