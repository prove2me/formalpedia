-- Prove2me | solution 1 for GlobalTheory.T.exists_reversedCharpolyCoeff_not_mem_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:55:59.846394+00:00
-- url     : https://prove2.me/submissions/0e5c06ac-9d5d-460e-992c-123a588911ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsReversedCharpolyCoeffNotMemPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsReversedCharpolyCoeffNotMemPrimeStatement
import Theorems.Thm_GlobalTheory_NormalDescent_exists_normCoeff_not_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (b : B), (∃ Q : Ideal B, Q.IsPrime ∧ Q.comap φ = ⊥) → ∀ p : Ideal A, p.IsPrime →
    (∀ Q : Ideal B, Q.IsPrime → Q.comap φ = p → b ∉ Q) → ∃ k, 1 ≤ k ∧ normCoeff φ hφ b k ∉ p := by
  first | exact @GlobalTheory.NormalDescent.exists_normCoeff_not_mem | exact GlobalTheory.NormalDescent.exists_normCoeff_not_mem | (intros; apply GlobalTheory.NormalDescent.exists_normCoeff_not_mem <;> assumption)
end _root_.GlobalTheory.T
