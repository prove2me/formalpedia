-- Prove2me | solution 1 for GlobalTheory.exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:56.387974+00:00
-- url     : https://prove2.me/submissions/c3a1f48c-3e4f-445c-8046-b01a3b6f826f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type*} [CommRing S]
    {q : Ideal S} (hq : q ∈ minimalPrimes S) (m : Ideal S) [m.IsPrime] (hqm : q ≤ m)
    [IsDomain (Localization.AtPrime m)] {x : S} (hx : x ∈ q) :
    ∃ s : m.primeCompl, (s : S) * x = 0 := by
  have hPq : (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) ≤ q := by
    intro y hy
    have hy0 : algebraMap S (Localization.AtPrime m) y = 0 := hy
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ y).1 hy0
    have hsy : (s : S) * y ∈ q := by
      rw [hs]
      exact q.zero_mem
    have hsq : (s : S) ∉ q := fun h => s.2 (hqm h)
    exact (hq.1.1.mem_or_mem hsy).resolve_left hsq
  have hqP : q ≤ (⊥ : Ideal (Localization.AtPrime m)).comap (algebraMap S _) :=
    hq.2 ⟨Ideal.comap_isPrime _ _, bot_le⟩ hPq
  have hx0 : algebraMap S (Localization.AtPrime m) x = 0 := hqP hx
  exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).1 hx0
end GlobalTheory
