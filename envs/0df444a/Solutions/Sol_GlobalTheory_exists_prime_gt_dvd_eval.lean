-- Prove2me | solution 1 for GlobalTheory.exists_prime_gt_dvd_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:52.769801+00:00
-- url     : https://prove2.me/submissions/50f35fcd-6084-4a57-a3cb-f28ac8f6bcdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeGtDvdEval
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLargePrimeDvdIntPolynomialEval
import Theorems.Thm_GlobalTheory_PrimeDivisorOfPolynomialValue_exists_prime_gt_dvd_eval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
open GlobalTheory
open Polynomial
namespace GlobalTheory
theorem _root_.solution :
    ∀ f : ℤ[X], 0 < f.natDegree → ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, (p : ℤ) ∣ f.eval x := by
  first
  | exact @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval
  | (apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeDivisorOfPolynomialValue.exists_prime_gt_dvd_eval ..)
end GlobalTheory
