-- Prove2me | solution 1 for GlobalTheory.Hk.LamRay.pow_prime_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:49.591017+00:00
-- url     : https://prove2.me/submissions/9949c862-624c-4b3f-8e4b-04ef1a0b8c26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
import Theorems.Thm_GlobalTheory_Mem_FewPrimes_exists_prime_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.LamRay
theorem _root_.solution (hK : Module.finrank ℚ K = 2) {P : Ideal (𝓞 K)} {k : ℕ} (hP : P.IsPrime) (h0 : P ≠ ⊥)
    (hk : 1 ≤ k) : IsPrimePow (Ideal.absNorm (P ^ k)) ∧
      P ∣ Ideal.span {((Ideal.absNorm (P ^ k)).minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm P := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP, h0⟩
  obtain ⟨p, hp, hm⟩ := GlobalTheory.Mem.FewPrimes.exists_prime_mem v
  have hd : P ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_span_singleton.2 hm
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK]
  have h1 : 1 < Ideal.absNorm P := NumberField.HeightOneSpectrum.one_lt_absNorm v
  have h2 : Ideal.absNorm P ∣ p ^ 2 := hN ▸ map_dvd _ hd
  obtain ⟨i, -, he⟩ := (Nat.dvd_prime_pow hp).1 h2
  have hi : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at he
    exact absurd he h1.ne'
  have hik : i * k ≠ 0 := mul_ne_zero hi (by omega)
  rw [map_pow, he, ← pow_mul, hp.pow_minFac hik]
  exact ⟨(isPrimePow_nat_iff _).2 ⟨p, i * k, hp, Nat.pos_of_ne_zero hik, rfl⟩, hd, he ▸ h1⟩
end GlobalTheory.Hk.LamRay
