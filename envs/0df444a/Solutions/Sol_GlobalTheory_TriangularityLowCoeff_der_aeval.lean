-- Prove2me | solution 1 for GlobalTheory.TriangularityLowCoeff.der_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:59.86167+00:00
-- url     : https://prove2.me/submissions/1bb7047d-250a-4a19-a5fc-f1fd5667dc35

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
    (D : Derivation R B B) (y : Fin d → B) (Q : MvPolynomial (Fin d) R) :
    D (aeval y Q) = ∑ j, aeval y (pderiv j Q) * D (y j) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, aeval_X, D.leibniz, hp, smul_eq_mul, smul_eq_mul]
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp
end GlobalTheory.TriangularityLowCoeff
