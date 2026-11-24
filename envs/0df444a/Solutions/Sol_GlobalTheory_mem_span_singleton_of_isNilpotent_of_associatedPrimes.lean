-- Prove2me | solution 1 for GlobalTheory.mem_span_singleton_of_isNilpotent_of_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:21:35.264814+00:00
-- url     : https://prove2.me/submissions/690c7a87-5fdb-40a3-9062-1c56d306790a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R]
    [IsNoetherianRing R] (x : R)
    (hP : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      IsDomain (Localization.AtPrime P))
    {n : R} (hn : IsNilpotent n) : n ∈ Ideal.span {x} := by
  by_contra hnx
  have h0 : (Ideal.Quotient.mk (Ideal.span {x}) n) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hPa, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (Ideal.span {x}) n) h0
  haveI : P.IsPrime := hPa.isPrime
  haveI := hP P hPa
  have hz : algebraMap R (Localization.AtPrime P) n = 0 :=
    (hn.map (algebraMap R (Localization.AtPrime P))).eq_zero
  obtain ⟨⟨s, hs⟩, hsn⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ n).1 hz
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk (Ideal.span {x}) s * Ideal.Quotient.mk (Ideal.span {x}) n = 0
  rw [← map_mul, hsn, map_zero]
end GlobalTheory
