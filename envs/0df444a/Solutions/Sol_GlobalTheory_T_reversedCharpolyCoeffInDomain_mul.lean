-- Prove2me | solution 1 for GlobalTheory.T.reversedCharpolyCoeffInDomain_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:21.517825+00:00
-- url     : https://prove2.me/submissions/1a3d4f86-e8df-4923-8254-5978b881a0fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffInDomainMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ReversedCharpolyCoeffInDomainMulStatement
import Theorems.Thm_GlobalTheory_NormalDescent_normCoeff_mul


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
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_mul | exact GlobalTheory.NormalDescent.normCoeff_mul | (intros; apply GlobalTheory.NormalDescent.normCoeff_mul <;> assumption)
end _root_.GlobalTheory.T
