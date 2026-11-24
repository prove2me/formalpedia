-- Prove2me | solution 1 for GlobalTheory.optionEquivLeft_pderiv_none
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:17.744526+00:00
-- url     : https://prove2.me/submissions/8610bffd-629a-4a4f-af63-ee37de8a753a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StandardEtaleMvPolynomialHypersurface

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution (A : Type) [CommRing A] (n : ℕ)
    (p : MvPolynomial (Option (Fin n)) A) :
    optionEquivLeft A (Fin n) (pderiv none p) = Polynomial.derivative (optionEquivLeft A (Fin n) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with _ | j
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]
end GlobalTheory
