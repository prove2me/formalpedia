-- Prove2me | solution 1 for GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:08:15.091746+00:00
-- url     : https://prove2.me/submissions/47efe1a9-6f3d-4257-82dd-e052e4fe6cbf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PosDefConjTransposeMulSelfEqExpPolynomial
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PosDefConjTransposeMulSelfEqExpPolynomialStatement
import Theorems.Thm_GlobalTheory_posDef_conjTranspose_mul_self_eq_exp_polynomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  first | exact @GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | exact GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | (intros; apply GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial <;> assumption)
end _root_.GlobalTheory.T
