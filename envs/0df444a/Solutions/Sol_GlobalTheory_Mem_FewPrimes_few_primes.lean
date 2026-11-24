-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.few_primes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:50.832377+00:00
-- url     : https://prove2.me/submissions/86085e54-6e1f-46d2-b197-1a06a8e18de9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_finite_absNorm_le
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_ncard_not_prime_le
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_ncard_absNorm_eq_le
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_ncard_dvd_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.FewPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.FewPrimes
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 → (∀ X : ℝ, 1 ≤ X → {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite ∧ ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧ ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X) ∧ (∀ p : ℕ, p.Prime → {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2) ∧ ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤ 3 * Real.log (4 * Ideal.absNorm 𝔮) :=
  fun _ _ _ _ hK => ⟨fun X _ => ⟨finite_absNorm_le X, ncard_not_prime_le hK X⟩,
    ncard_absNorm_eq_le hK, ncard_dvd_le⟩
end GlobalTheory.Mem.FewPrimes
