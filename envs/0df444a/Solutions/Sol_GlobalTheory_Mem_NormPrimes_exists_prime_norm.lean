-- Prove2me | solution 1 for GlobalTheory.Mem.NormPrimes.exists_prime_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:06.186802+00:00
-- url     : https://prove2.me/submissions/d516be5c-309d-4a2c-94a0-75e9633ea099

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonemptyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeElementCongruent
import Theorems.Thm_GlobalTheory_Mem_NormPrimes_exists_prime_norm_of_two_le

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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.NormPrimes
namespace GlobalTheory.Mem.NormPrimes
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), M ≠ 0 → ∀ (a : 𝓞 K), IsCoprime a (M : 𝓞 K) → ∀ N : ℕ, ∃ (π : 𝓞 K) (p : ℕ), p.Prime ∧ N < p ∧ Algebra.norm ℤ π = p ∧ π - a ∈ Ideal.span {(M : 𝓞 K)} := by
  intro K _ _ _ h2 M hM a ha N
  rcases Nat.lt_or_ge M 2 with h | h
  · obtain rfl : M = 1 := by omega
    obtain ⟨π, p, hp, hN, hn, -⟩ := exists_prime_norm_of_two_le K h2 2 le_rfl 1 isCoprime_one_left N
    exact ⟨π, p, hp, hN, hn, by simp⟩
  · exact exists_prime_norm_of_two_le K h2 M h a ha N
end GlobalTheory.Mem.NormPrimes
