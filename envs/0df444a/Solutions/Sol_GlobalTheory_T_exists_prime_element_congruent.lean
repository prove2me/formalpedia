-- Prove2me | solution 1 for GlobalTheory.T.exists_prime_element_congruent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:38:21.85172+00:00
-- url     : https://prove2.me/submissions/3330ff7c-4dd2-4c2c-bbf9-40cbd7f5fc3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeElementCongruent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeElementCongruentStatement
import Theorems.Thm_GlobalTheory_Mem_NormPrimes_exists_prime_norm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  first | exact @GlobalTheory.Mem.NormPrimes.exists_prime_norm | exact GlobalTheory.Mem.NormPrimes.exists_prime_norm | (intros; apply GlobalTheory.Mem.NormPrimes.exists_prime_norm <;> assumption)
end _root_.GlobalTheory.T
