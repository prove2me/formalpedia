-- Prove2me | solution 1 for GlobalTheory.isIntegrallyClosed_quotient_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:03:31.943722+00:00
-- url     : https://prove2.me/submissions/45f1ec5a-6294-418d-8282-18051751e119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_IsIntegrallyClosedQuotientOfMemMinimalPrimes
import Theorems.Thm_GlobalTheory_exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime

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
    (hS : ∀ (m : Ideal S) [m.IsPrime],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m))
    {q : Ideal S} (hq : q ∈ minimalPrimes S) : IsIntegrallyClosed (S ⧸ q) := by
  have : q.IsPrime := hq.1.1
  refine IsIntegrallyClosed.of_localization_maximal (fun M _ _ => ?_)
  let m : Ideal S := M.comap (Ideal.Quotient.mk q)
  have : m.IsPrime := Ideal.comap_isPrime _ _
  have hqm : q ≤ m := by
    intro x hx
    show Ideal.Quotient.mk q x ∈ M
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact M.zero_mem
  obtain ⟨hdom, hic⟩ := hS m
  have hker : ∀ x ∈ q, algebraMap S (Localization.AtPrime m) x = 0 := by
    intro x hx
    obtain ⟨s, hs⟩ := exists_mul_eq_zero_of_mem_minimalPrimes_of_isDomain_atPrime hq m hqm hx
    exact (IsLocalization.map_eq_zero_iff m.primeCompl _ x).2 ⟨s, hs⟩
  let : Algebra (S ⧸ q) (Localization.AtPrime m) :=
    (Ideal.Quotient.lift q (algebraMap S (Localization.AtPrime m)) hker).toAlgebra
  have hmk : ∀ a : S, algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q a) =
      algebraMap S (Localization.AtPrime m) a := fun a => Ideal.Quotient.lift_mk _ _ _
  have : IsLocalization M.primeCompl (Localization.AtPrime m) := by
    refine (isLocalization_iff _ _).2 ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
      show IsUnit (algebraMap (S ⧸ q) (Localization.AtPrime m) (Ideal.Quotient.mk q s))
      rw [hmk]
      exact IsLocalization.map_units (Localization.AtPrime m) (⟨s, hy⟩ : m.primeCompl)
    · intro z
      obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj m.primeCompl z
      refine ⟨⟨Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q s, s.2⟩⟩, ?_⟩
      show z * algebraMap (S ⧸ q) _ (Ideal.Quotient.mk q s) =
        algebraMap (S ⧸ q) _ (Ideal.Quotient.mk q a)
      rw [hmk, hmk]
      exact h
    · intro a b hab
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [hmk, hmk] at hab
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists m.primeCompl _).1 hab
      refine ⟨⟨Ideal.Quotient.mk q c, c.2⟩, ?_⟩
      show Ideal.Quotient.mk q c * Ideal.Quotient.mk q a =
        Ideal.Quotient.mk q c * Ideal.Quotient.mk q b
      rw [← map_mul, ← map_mul, hc]
  exact hic.of_equiv (IsLocalization.algEquiv M.primeCompl (Localization.AtPrime M)
    (Localization.AtPrime m)).toRingEquiv.symm
end GlobalTheory
