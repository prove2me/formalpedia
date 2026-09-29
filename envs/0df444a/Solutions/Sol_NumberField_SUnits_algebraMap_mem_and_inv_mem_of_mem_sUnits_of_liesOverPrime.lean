-- Prove2me | solution 1 for NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c9106b83-46f5-5fe3-8eee-ef0b6b5e282d

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime

set_option autoImplicit false
open NumberField IsDedekindDomain

namespace SUnitVal

open IsDedekindDomain

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (A : ValuationSubring (AlgebraicClosure ℚ))

lemma algebraMap_integer_mem (a : 𝓞 ↥F) : algebraMap ↥F (AlgebraicClosure ℚ) (a : ↥F) ∈ A := by
  obtain ⟨pz, hmon, hev⟩ := NumberField.RingOfIntegers.isIntegral a
  have hev' : Polynomial.eval₂ (algebraMap ℤ (AlgebraicClosure ℚ)) (algebraMap ↥F (AlgebraicClosure ℚ) (a : ↥F)) pz = 0 := by
    have := congrArg ((algebraMap ↥F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 ↥F) ↥F)) hev
    rw [Polynomial.hom_eval₂, map_zero,
      RingHom.ext_int (((algebraMap ↥F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 ↥F) ↥F)).comp (algebraMap ℤ (𝓞 ↥F)))
        (algebraMap ℤ (AlgebraicClosure ℚ))] at this
    exact this
  have h2 : IsIntegral A (algebraMap ↥F (AlgebraicClosure ℚ) (a : ↥F)) := by
    refine ⟨pz.map (algebraMap ℤ A), hmon.map _, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (algebraMap ℤ A)) (algebraMap ℤ (AlgebraicClosure ℚ))]
    exact hev'
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).1 h2
  rw [← hy]
  exact y.2

noncomputable def toA : 𝓞 ↥F →+* A where
  toFun a := ⟨algebraMap ↥F (AlgebraicClosure ℚ) (a : ↥F), algebraMap_integer_mem F A a⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

lemma coe_toA (a : 𝓞 ↥F) : ((toA F A a : A) : AlgebraicClosure ℚ) = algebraMap ↥F (AlgebraicClosure ℚ) (a : ↥F) := rfl

noncomputable def centre : Ideal (𝓞 ↥F) := (IsLocalRing.maximalIdeal A).comap (toA F A)

scoped instance : (centre F A).IsPrime := Ideal.comap_isPrime _ _

lemma natCast_mem_centre (q : ℕ) (hA : A.LiesOverPrime q) : ((q : ℕ) : 𝓞 ↥F) ∈ centre F A := by
  change toA F A q ∈ IsLocalRing.maximalIdeal A
  rw [map_natCast]
  have h : ((q : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    have : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by simp
    rw [this]
    exact hA
  exact (ValuationSubring.coe_mem_nonunits_iff).1 h

lemma algebraMap_mem_of_eq_mul_inv (a s : 𝓞 ↥F) (hs : s ∉ centre F A) (y : ↥F)
    (hy : y = algebraMap (𝓞 ↥F) ↥F a * (algebraMap (𝓞 ↥F) ↥F s)⁻¹) : algebraMap ↥F (AlgebraicClosure ℚ) y ∈ A := by
  have hunit : IsUnit (toA F A s) := by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨t, ht⟩ := hunit.exists_right_inv
  have hts : (algebraMap ↥F (AlgebraicClosure ℚ) (algebraMap (𝓞 ↥F) ↥F s))⁻¹ = (t : AlgebraicClosure ℚ) := by
    have h1 : algebraMap ↥F (AlgebraicClosure ℚ) (algebraMap (𝓞 ↥F) ↥F s) * (t : AlgebraicClosure ℚ) = 1 := by
      have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) ht
      simpa [coe_toA] using this
    exact (eq_inv_of_mul_eq_one_right h1).symm
  rw [hy, map_mul, map_inv₀, hts]
  exact A.mul_mem _ _ (algebraMap_integer_mem F A a) t.2

end SUnitVal
p2m_reactivate "P2MW.S_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime.SUnitVal"

open SUnitVal IsDedekindDomain in
theorem solution
    (S : Finset Nat.Primes) (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F]
    (u : (↥F)ˣ) (hu : u ∈ NumberField.SUnits.sUnits ℚ ↥F Sℚ)
    (q : Nat.Primes) (hq : q ∉ S) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime (q : ℕ)) :
    algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F) ∈ A ∧ (algebraMap ↥F (AlgebraicClosure ℚ) (u : ↥F))⁻¹ ∈ A := by
  classical

  have hq_mem : ((q : ℕ) : 𝓞 ↥F) ∈ centre F A := natCast_mem_centre F A q hA
  have hne : centre F A ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hq_mem
    exact q.2.ne_zero (by exact_mod_cast hq_mem)
  let v₀ : HeightOneSpectrum (𝓞 ↥F) := ⟨centre F A, inferInstance, hne⟩
  have hv₀S : v₀.under (𝓞 ℚ) ∉ Sℚ := by
    intro hmem
    have hmem' : v₀.under (𝓞 ℚ) ∈ NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes) := by
      rw [← hSℚ]; exact hmem
    obtain ⟨p', hp'S, hp'⟩ := (NumberField.mem_placesOverPrimes_iff ℚ _ _).1 hmem'
    have hp'mem : ((p' : ℕ) : 𝓞 ↥F) ∈ centre F A := by
      have := Ideal.mem_comap.1 hp'
      rwa [map_natCast] at this
    have hneq : (p' : ℕ) ≠ q := fun h => hq (by rwa [show p' = q from Subtype.ext h] at hp'S)
    have hcop : IsCoprime ((p' : ℕ) : ℤ) ((q : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes p'.2 q.2).2 hneq)
    obtain ⟨a, b, hab⟩ := hcop
    apply (inferInstance : (centre F A).IsPrime).ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 ↥F) = (a : 𝓞 ↥F) * ((p' : ℕ) : 𝓞 ↥F) + (b : 𝓞 ↥F) * ((q : ℕ) : 𝓞 ↥F) := by
      have := congrArg (Int.cast : ℤ → 𝓞 ↥F) hab
      push_cast at this
      exact this.symm
    rw [h1]
    exact (centre F A).add_mem ((centre F A).mul_mem_left _ hp'mem) ((centre F A).mul_mem_left _ hq_mem)

  have hval : v₀.valuation ↥F (u : ↥F) = 1 := by
    have := (NumberField.SUnits.mem_sUnits_iff ℚ ↥F Sℚ u).1 hu 1 v₀ hv₀S
    simpa using this

  have key : ∀ y : ↥F, v₀.valuation ↥F y ≤ 1 → algebraMap ↥F (AlgebraicClosure ℚ) y ∈ A := by
    intro y hy
    have hmem : y ∈ HeightOneSpectrum.valuationSubringAtPrime ↥F v₀ := by
      rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
      exact (Valuation.mem_valuationSubring_iff _ _).2 hy
    obtain ⟨a, s, hs, hys⟩ : ∃ (a s : 𝓞 ↥F) (_ : s ∈ v₀.asIdeal.primeCompl),
        y = algebraMap (𝓞 ↥F) ↥F a * (algebraMap (𝓞 ↥F) ↥F s)⁻¹ := hmem
    exact algebraMap_mem_of_eq_mul_inv F A a s hs y hys
  refine ⟨key _ hval.le, ?_⟩
  rw [← map_inv₀]
  refine key _ ?_
  rw [map_inv₀, hval, inv_one]

end S_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
end P2MW
export P2MW.S_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime (solution)
