-- Prove2me | solution 1 for GlobalTheory.T.summable_inv_absNorm_primes_of_not_prime_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:20.200673+00:00
-- url     : https://prove2.me/submissions/9aaf497f-7b9f-4a37-aaf6-fac64af4d849

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNormStatement
import Theorems.Thm_GlobalTheory_summable_inv_absNorm_of_not_prime


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K], Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} => ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  first | exact @GlobalTheory.summable_inv_absNorm_of_not_prime | exact GlobalTheory.summable_inv_absNorm_of_not_prime | (intros; apply GlobalTheory.summable_inv_absNorm_of_not_prime <;> assumption)
end _root_.GlobalTheory.T
