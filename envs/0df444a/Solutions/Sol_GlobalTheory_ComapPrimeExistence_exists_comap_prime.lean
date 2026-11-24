-- Prove2me | solution 1 for GlobalTheory.ComapPrimeExistence.exists_comap_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:04.120556+00:00
-- url     : https://prove2.me/submissions/40ddaa76-269f-41e3-9813-a57801c48b7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsComapPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ComapPrimeExistence
open NumberField IsDedekindDomain
namespace GlobalTheory.ComapPrimeExistence
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (φ : E →+* K) (w : HeightOneSpectrum (RingOfIntegers K)) :
    ∃ Q : HeightOneSpectrum (RingOfIntegers E), ∀ r : RingOfIntegers E,
      r ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingHom φ : RingOfIntegers E → RingOfIntegers K) r ∈ w.asIdeal := by
  have hp := w.isPrime
  refine ⟨⟨w.asIdeal.comap (RingOfIntegers.mapRingHom φ), Ideal.comap_isPrime _ _, ?_⟩,
    fun r => Ideal.mem_comap⟩
  intro h
  have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hmem : ((Ideal.absNorm w.asIdeal : ℕ) : RingOfIntegers E) ∈
      w.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hmem
  exact hn (Nat.cast_eq_zero.mp hmem)
end GlobalTheory.ComapPrimeExistence
