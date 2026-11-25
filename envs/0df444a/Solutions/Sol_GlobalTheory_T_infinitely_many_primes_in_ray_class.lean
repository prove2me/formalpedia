-- Prove2me | solution 1 for GlobalTheory.T.infinitely_many_primes_in_ray_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:48:58.57746+00:00
-- url     : https://prove2.me/submissions/6681feb7-ddcb-46cf-b38d-6b1b477b769a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClassStatement
import Theorems.Thm_GlobalTheory_Mem_RayPrimes_exists_prime_in_class


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
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (c : D.G) (N : ℕ), ∃ v : D.Pr, D.cls v.1.asIdeal = c ∧ (Ideal.absNorm v.1.asIdeal).Prime ∧ N < Ideal.absNorm v.1.asIdeal := by
  first | exact @GlobalTheory.Mem.RayPrimes.exists_prime_in_class | exact GlobalTheory.Mem.RayPrimes.exists_prime_in_class | (intros; apply GlobalTheory.Mem.RayPrimes.exists_prime_in_class <;> assumption)
end _root_.GlobalTheory.T
