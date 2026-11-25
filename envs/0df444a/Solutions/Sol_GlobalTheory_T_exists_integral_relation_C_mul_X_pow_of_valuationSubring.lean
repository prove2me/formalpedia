-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_relation_C_mul_X_pow_of_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:16:58.462072+00:00
-- url     : https://prove2.me/submissions/89e2b4a1-7522-42f7-a042-ed1aabde70d7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralConeRingOfForallValuationSubring
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegralConeRingOfForallValuationSubringStatement
import Theorems.Thm_GlobalTheory_isIntegral_coneRing_of_forall_valuationSubring


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  first | exact @GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | exact GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring | (intros; apply GlobalTheory.isIntegral_coneRing_of_forall_valuationSubring <;> assumption)
end _root_.GlobalTheory.T
