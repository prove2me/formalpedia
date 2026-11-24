-- Prove2me | solution 1 for GlobalTheory.PrimeInHeightOneSpectrum.exists_prime_mem_heightOneSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:44:40.628807+00:00
-- url     : https://prove2.me/submissions/1295f424-64db-428d-9f79-0a9ddda93850

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Theorems.Thm_GlobalTheory_PrimeInHeightOneSpectrum_exists_prime_natCast_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeInHeightOneSpectrum
namespace GlobalTheory.PrimeInHeightOneSpectrum
theorem _root_.solution {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)
end GlobalTheory.PrimeInHeightOneSpectrum
