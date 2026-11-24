-- Prove2me | solution 1 for GlobalTheory.CotangentSquare.det_ne_zero_of_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:06:53.825686+00:00
-- url     : https://prove2.me/submissions/6d2c200f-4013-4671-bf6d-7f0aa83bdd32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.CotangentSquare
open MvPolynomial
variable {O B σ : Type} [CommRing O] [CommRing B]
namespace GlobalTheory.CotangentSquare
theorem _root_.solution [Fintype σ] [DecidableEq σ] [IsDomain O] {N J : Matrix σ σ O}
    {c : O} (hc : c ≠ 0) (h : N * J = c • (1 : Matrix σ σ O)) : J.det ≠ 0 := by
  intro hJ
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, hJ, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm
end GlobalTheory.CotangentSquare
