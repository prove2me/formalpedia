-- Prove2me | solution 1 for GlobalTheory.T.exists_large_prime_sq_dvd_eval_of_separable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:44.47047+00:00
-- url     : https://prove2.me/submissions/a2c3e38a-532c-48db-baab-be3dba8d1af2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SepIntPolyRootModPrimeSqStatement
import Theorems.Thm_GlobalTheory_sep_int_poly_root_mod_prime_sq


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
theorem _root_.solution : ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  first | exact @GlobalTheory.sep_int_poly_root_mod_prime_sq | exact GlobalTheory.sep_int_poly_root_mod_prime_sq | (intros; apply GlobalTheory.sep_int_poly_root_mod_prime_sq <;> assumption)
end _root_.GlobalTheory.T
