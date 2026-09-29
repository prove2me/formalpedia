-- Prove2me | solution 1 for IsIntegrallyClosed.mem_span_singleton_of_mul_mem_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/ef61fbea-4fcb-57f6-94df-2506da5a66c3

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import Theorems.Thm_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral

open IsLocalRing

universe u

theorem solution
    {R A : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra R A] [FaithfulSMul R A] [Algebra.IsIntegral R A]
    {p : R} (hp : (Ideal.span {p}).IsPrime) (hp0 : p ≠ 0)
    {s : R} (hs : s ∉ Ideal.span {p}) {a : A}
    (h : algebraMap R A s * a ∈ Ideal.span {algebraMap R A p}) :
    a ∈ Ideal.span {algebraMap R A p} := by
  by_contra ha
  set x : A := algebraMap R A p with hx
  have hx0 : x ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R A)).mpr hp0
  have ha0 : (Ideal.Quotient.mk (Ideal.span {x}) a) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ ha0
  haveI := hP.isPrime
  have hPh : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hx0 P hP
  have hQh : (P.under R).height = 1 := by
    rw [← hPh]; exact (Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral R A P).symm

  have hpP : Ideal.span {p} ≤ P.under R := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    have := (show IsAssociatedPrime P (A ⧸ Ideal.span {x}) from hP).annihilator_le
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient] at this
    exact this (Ideal.subset_span rfl)

  have heq : Ideal.span {p} = P.under R := by
    rcases lt_or_eq_of_le hpP with hlt | h
    · exfalso
      haveI := hp
      have hle1 : (P.under R).height ≤ ((1 : ℕ) : ℕ∞) := by rw [hQh]; norm_cast
      have hlt1 := (Ideal.height_le_iff.mp hle1) (Ideal.span {p}) hp hlt
      have h0 : (Ideal.span {p}).height = 0 := by
        apply ENat.lt_one_iff_eq_zero.mp; exact_mod_cast hlt1
      have hmin : Ideal.span {p} ∈ (⊥ : Ideal R).minimalPrimes := Ideal.height_eq_zero_iff.mp h0
      have : Ideal.span {p} = ⊥ := by
        simpa [Ideal.minimalPrimes_eq_subsingleton_self] using hmin
      exact hp0 (by simpa using this)
    · exact h

  apply hs
  rw [heq, Ideal.mem_comap]
  apply hcol
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact h

end S_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral
end P2MW
export P2MW.S_IsIntegrallyClosed_mem_span_singleton_of_mul_mem_of_isIntegral (solution)
