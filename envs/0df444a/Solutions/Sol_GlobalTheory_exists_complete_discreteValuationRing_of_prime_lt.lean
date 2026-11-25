-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:12:44.849487+00:00
-- url     : https://prove2.me/submissions/6b258cc8-d202-4abc-b5d6-3c9f99f89542

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Theorems.Thm_GlobalTheory_exists_complete_discreteValuationRing_ker_eq

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
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution {A : Type u} [CommRing A]
    [IsNoetherianRing A] (q p : Ideal A) [q.IsPrime] [p.IsPrime] (hqp : q < p) :
    ∃ (O : Type u) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (maximalIdeal O) O) (φ : A →+* O),
      RingHom.ker φ = q ∧ (maximalIdeal O).comap φ = p := by
  let S := Localization.AtPrime p
  have hdis : Disjoint (p.primeCompl : Set A) q := by
    rw [Set.disjoint_left]
    exact fun x hx hx' => hx (hqp.le hx')
  have hq' : (q.map (algebraMap A S)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q inferInstance hdis
  have hc : (q.map (algebraMap A S)).comap (algebraMap A S) = q :=
    IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S inferInstance hdis
  have hm : (maximalIdeal S).comap (algebraMap A S) = p :=
    Localization.AtPrime.comap_maximalIdeal
  obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_ker_eq
    (q.map (algebraMap A S)) (fun h => hqp.ne (by rw [← hc, h, hm]))
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    φ.comp (algebraMap A S), ?_, ?_⟩
  · rw [← RingHom.comap_ker, h1, hc]
  · rw [← Ideal.comap_comap, maximalIdeal_comap, hm]
end GlobalTheory
