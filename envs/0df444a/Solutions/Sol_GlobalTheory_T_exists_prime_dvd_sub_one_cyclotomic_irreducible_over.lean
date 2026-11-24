-- Prove2me | solution 1 for GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:05.280201+00:00
-- url     : https://prove2.me/submissions/ee54fbf7-154d-4577-bb28-572905be0166

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOverStatement
import Theorems.Thm_GlobalTheory_exists_prime_dvd_sub_one_irreducible_cyclotomic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 → ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  first | exact @GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic | exact GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic | (intros; apply GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic <;> assumption)
end _root_.GlobalTheory.T
