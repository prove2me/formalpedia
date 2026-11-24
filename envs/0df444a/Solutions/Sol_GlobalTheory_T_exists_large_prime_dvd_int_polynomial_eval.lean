-- Prove2me | solution 1 for GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:39.38939+00:00
-- url     : https://prove2.me/submissions/7652dc4a-feb6-4559-aaa9-7ff80d361201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEval
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEvalStatement
import Theorems.Thm_GlobalTheory_PrimeDivisorOfPolynomialValue_exists_prime_gt_dvd_eval
import Theorems.Thm_GlobalTheory_exists_prime_gt_dvd_eval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first | exact @GlobalTheory.exists_prime_gt_dvd_eval | exact GlobalTheory.exists_prime_gt_dvd_eval | (intros; apply GlobalTheory.exists_prime_gt_dvd_eval <;> assumption)
end _root_.GlobalTheory.T
