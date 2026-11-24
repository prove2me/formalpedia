-- Prove2me | solution 1 for GlobalTheory.CompleteDVR.exists_place_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:06.5408+00:00
-- url     : https://prove2.me/submissions/25e378e8-9aea-49b2-afae-401d86588992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompleteDvrExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing HeightOneSpectrum
open GlobalTheory GlobalTheory.CompleteDVR
namespace GlobalTheory.CompleteDVR
theorem _root_.solution {K : Type} [Field K] [NumberField K] (W : ValuationSubring K) :
    ∃ la : HeightOneSpectrum (𝓞 K), (la.valuation K).valuationSubring ≤ W := by
  have hint : ∀ a : 𝓞 K, (a : K) ∈ W := fun a => by
    have h2 : IsIntegral W (a : K) := (RingOfIntegers.isIntegral_coe a).tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := K)).mp h2
    rw [← hy]
    exact y.2
  let g : 𝓞 K →+* W := (algebraMap (𝓞 K) K).codRestrict W hint
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal ((IsLocalRing.maximalIdeal W).comap g)
    (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal W).ne_top)
  refine ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField K)⟩,
    fun a ha => ?_⟩
  obtain ⟨n, d, hnd⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer _ a ha
  have hu : IsUnit (g d) := by
    by_contra hu
    exact d.2 (hle ((IsLocalRing.mem_maximalIdeal _).2 hu))
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : algebraMap (𝓞 K) K d * (b : K) = 1 := congrArg Subtype.val hb
  have : a = algebraMap (𝓞 K) K n * (b : K) := by rw [← hnd, mul_assoc, hb', mul_one]
  rw [this]
  exact W.mul_mem _ _ (hint n) b.2
end GlobalTheory.CompleteDVR
