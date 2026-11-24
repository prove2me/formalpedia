-- Prove2me | solution 1 for GlobalTheory.T.kernel_free_at_primes_of_constant_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:17:13.571323+00:00
-- url     : https://prove2.me/submissions/c2d4434f-9ec9-4ca1-bbfd-7e64ac0a42cb

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRank
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_KernelFreeAtPrimesOfConstantRankStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KerLocal_ker_baseChange_localization_free


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] (d : Q →ₗ[R] P) (g : ℕ), Module.Finite R (LinearMap.ker d) → Module.Projective R (LinearMap.ker d) → (∀ p : PrimeSpectrum R, Module.rankAtStalk (LinearMap.ker d) p = g) → ∀ (p : Ideal R) [p.IsPrime], Module.Free (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.Finite (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) ∧ Module.finrank (Localization.AtPrime p) (LinearMap.ker (d.baseChange (Localization.AtPrime p))) = g := by
  first | exact @GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | exact GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free | (intros; apply GlobalTheory.CompanionTheory.KerLocal.ker_baseChange_localization_free <;> assumption)
end _root_.GlobalTheory.T
