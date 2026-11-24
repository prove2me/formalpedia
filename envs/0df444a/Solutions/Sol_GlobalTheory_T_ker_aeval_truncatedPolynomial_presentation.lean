-- Prove2me | solution 1 for GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:03.1566+00:00
-- url     : https://prove2.me/submissions/8ea18b5d-9e14-4ed7-befa-ce337b0f0d11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalTruncatedPolynomialPresentation
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerAevalTruncatedPolynomialPresentationStatement
import Theorems.Thm_GlobalTheory_ker_aeval_truncated


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  first | exact @GlobalTheory.ker_aeval_truncated | exact GlobalTheory.ker_aeval_truncated | (intros; apply GlobalTheory.ker_aeval_truncated <;> assumption)
end _root_.GlobalTheory.T
