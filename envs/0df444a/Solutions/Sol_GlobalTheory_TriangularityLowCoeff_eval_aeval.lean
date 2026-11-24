-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.eval_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:01.457111+00:00
-- url     : https://prove2.me/submissions/238b8243-6eb6-4e8f-a612-88b4a424baa8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffAnnihilatedOfAevalMemKerPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TriangularityLowCoeff
open MvPolynomial
namespace GlobalTheory.TriangularityLowCoeff
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (Q : MvPolynomial (Fin d) R) :
    ε (aeval y Q) = coeff 0 Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hy, coeff_mul_X']
end GlobalTheory.TriangularityLowCoeff
