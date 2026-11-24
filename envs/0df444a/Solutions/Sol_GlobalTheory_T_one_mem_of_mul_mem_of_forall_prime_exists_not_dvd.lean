-- Prove2me | solution 1 for GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:19:34.752801+00:00
-- url     : https://prove2.me/submissions/358037cd-ab6c-4aa1-8928-6510ea5af669

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_OneMemOfMulMemOfForallPrimeNotDvdStatement
import Theorems.Thm_GlobalTheory_one_mem_of_mul_mem_of_forall_prime_not_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [Finite X] (S : AddSubgroup (X → ℤ)), (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) → (∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) → (1 : X → ℤ) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | exact GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | (intros; apply GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd <;> assumption)
end _root_.GlobalTheory.T
