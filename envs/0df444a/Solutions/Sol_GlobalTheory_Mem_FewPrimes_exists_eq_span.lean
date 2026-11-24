-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.exists_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:52.172163+00:00
-- url     : https://prove2.me/submissions/f533dd3b-7611-43c1-b88c-ca2bd93d9915

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_exists_prime_mem

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
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by
  obtain ⟨p, hp, hm⟩ := exists_prime_mem v
  have hd : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have h1 := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm v.asIdeal ∣ p ^ 2 := hN ▸ map_dvd _ hd
  obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have h3 : Ideal.absNorm v.asIdeal = p ^ 2 := by
    interval_cases i
    · rw [pow_zero] at he; exact absurd he h1.ne'
    · rw [pow_one] at he; exact absurd (he ▸ hp) hv
    · exact he
  refine ⟨p, hp, ?_, h3⟩
  obtain ⟨J, hJ⟩ := hd
  have h4 : Ideal.absNorm J = 1 := by
    have h5 := hN
    rw [hJ, map_mul, h3] at h5
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (by rw [h5, mul_one])
  rw [Ideal.absNorm_eq_one_iff] at h4
  rw [hJ, h4, Ideal.mul_top]
end GlobalTheory.Mem.FewPrimes
