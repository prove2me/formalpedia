-- Prove2me | solution 1 for IsCyclotomicExtension.exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8d3eddbe-6954-58df-b37b-6a20af30af50

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing

set_option autoImplicit false

namespace RamIdxCyc

open IsLocalRing NumberField

section Embed

variable {L : Type} [Field L] (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]

theorem exists_algebraMap_eq_of_isIntegral_int {x : L} (hx : IsIntegral ℤ x) : ∃ a : A, algebraMap A L a = x :=
  IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top

variable [NumberField L]

noncomputable def embFun (x : NumberField.RingOfIntegers L) : A :=
  Classical.choose (exists_algebraMap_eq_of_isIntegral_int A x.isIntegral_coe)

omit [NumberField L] in
@[scoped simp] theorem algebraMap_embFun (x : NumberField.RingOfIntegers L) : algebraMap A L (embFun A x) = (x : L) :=
  Classical.choose_spec (exists_algebraMap_eq_of_isIntegral_int A x.isIntegral_coe)

noncomputable def emb : NumberField.RingOfIntegers L →+* A where
  toFun := embFun A
  map_one' := IsFractionRing.injective A L (by simp)
  map_mul' x y := IsFractionRing.injective A L (by simp)
  map_zero' := IsFractionRing.injective A L (by simp)
  map_add' x y := IsFractionRing.injective A L (by simp)

omit [NumberField L] in
@[scoped simp] theorem algebraMap_emb (x : NumberField.RingOfIntegers L) : algebraMap A L (emb A x) = (x : L) :=
  algebraMap_embFun A x

end Embed

end RamIdxCyc
p2m_reactivate "P2MW.S_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing.RamIdxCyc"

open NumberField in

theorem solution
    (q ℓ : ℕ) [Fact q.Prime] [Fact ℓ.Prime] (hqℓ : q ≠ ℓ)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ}) :
    ∃ ε : A, IsUnit ε ∧ ϖ ^ (q - 1) = ε * (q : A) := by
  classical
  have hq : q.Prime := Fact.out
  have hl : ℓ.Prime := Fact.out
  haveI : NeZero (q * ℓ) := ⟨mul_ne_zero hq.ne_zero hl.ne_zero⟩
  haveI : NumberField L := IsCyclotomicExtension.numberField {q * ℓ} ℚ L

  set φ : (𝓞 L) →+* A := RamIdxCyc.emb A with hφdef
  have hφ : ∀ x : (𝓞 L), algebraMap A L (φ x) = (x : L) := RamIdxCyc.algebraMap_emb A

  set Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap φ with hQdef
  haveI hQprime : Q.IsPrime := Ideal.comap_isPrime φ _
  have hqQ : (q : (𝓞 L)) ∈ Q := by
    rw [hQdef, Ideal.mem_comap, map_natCast]; exact hAq
  haveI hQover : Q.LiesOver (Ideal.span {(q : ℤ)}) := by
    rw [Ideal.liesOver_iff, Ideal.under_def]
    refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime q) Ideal.IsPrime.ne_top' ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
    exact hqQ
  have hq0O : (q : (𝓞 L)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
  have hQbot : Q ≠ ⊥ := fun h => hq0O (by simpa [h] using hqQ)
  haveI hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal hQprime hQbot

  have hnd : ¬ q ∣ ℓ := fun h => hqℓ ((Nat.prime_dvd_prime_iff_eq hq hl).mp h)
  have he : Ideal.ramificationIdx' (Ideal.span {(q : ℤ)}) Q = q - 1 := by
    have h := IsCyclotomicExtension.Rat.ramificationIdx_eq (n := q * ℓ) (K := L) (P := Q) (p := q) (k := 0)
      (m := ℓ) (by ring) hnd
    rw [pow_zero, one_mul] at h
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(q : ℤ)}) (q := Q)
      (by simpa using Int.natCast_ne_zero.mpr hq.ne_zero)]
    exact h

  have hmap : (Ideal.span {(q : ℤ)}).map (algebraMap ℤ (𝓞 L)) = Ideal.span {(q : (𝓞 L))} := by
    rw [Ideal.map_span, Set.image_singleton, algebraMap_int_eq, map_natCast]
  have hmapbot : (Ideal.span {(q : ℤ)}).map (algebraMap ℤ (𝓞 L)) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hq0O
  obtain ⟨I, hQI, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmapbot Q
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapbot hQprime hQbot, he, hmap] at hfac
  have hIQ : ¬ I ≤ Q := fun h => Ideal.IsPrime.ne_top' (show Q = ⊤ by rw [← hQI]; exact (sup_eq_left.mpr h).symm)

  have hunit : ∀ s : (𝓞 L), s ∉ Q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

  let B := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing B := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) hQbot B
  have hinjOL : Function.Injective (algebraMap (𝓞 L) L) := IsFractionRing.injective (𝓞 L) L
  have hunitL : ∀ s : Q.primeCompl, IsUnit (algebraMap (𝓞 L) L s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h => s.2 (by
      have hs0 : (s : (𝓞 L)) = 0 := hinjOL (by rw [h, map_zero])
      rw [hs0]; exact Q.zero_mem))
  letI algBL : Algebra B L := (IsLocalization.lift (M := Q.primeCompl) (S := B) (g := algebraMap (𝓞 L) L) hunitL).toAlgebra
  haveI : IsScalarTower (𝓞 L) B L := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.lift_eq (M := Q.primeCompl) (S := B) (g := algebraMap (𝓞 L) L) hunitL x).symm)
  haveI : IsFractionRing B L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl B L

  have hqB : Ideal.span {(q : B)} = (IsLocalRing.maximalIdeal B) ^ (q - 1) := by
    have h := congrArg (Ideal.map (algebraMap (𝓞 L) B)) hfac
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_mul, Ideal.map_pow,
      IsLocalization.AtPrime.map_eq_top_of_not_le B hIQ, Ideal.mul_top,
      Localization.AtPrime.map_eq_maximalIdeal] at h
    exact h

  let ψ : B →+* A := IsLocalization.lift (M := Q.primeCompl) (S := B) (g := φ) (fun s => hunit s s.2)
  have hψ : ∀ x : (𝓞 L), ψ (algebraMap (𝓞 L) B x) = φ x := fun x => IsLocalization.lift_eq _ x
  have hψL : ∀ b : B, algebraMap A L (ψ b) = algebraMap B L b := fun b => by
    refine RingHom.congr_fun (IsLocalization.ringHom_ext Q.primeCompl (j := (algebraMap A L).comp ψ) (k := algebraMap B L) ?_) b
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply, hψ, hφ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

  let A' : ValuationSubring L := (ValuationRing.valuation A L).valuationSubring
  let B' : ValuationSubring L := (ValuationRing.valuation B L).valuationSubring
  have hA'mem : ∀ x : L, x ∈ A' ↔ ∃ a : A, algebraMap A L a = x := fun x => by
    rw [Valuation.mem_valuationSubring_iff, ← Valuation.mem_integer_iff]; exact ValuationRing.mem_integer_iff A L x
  have hB'mem : ∀ x : L, x ∈ B' ↔ ∃ b : B, algebraMap B L b = x := fun x => by
    rw [Valuation.mem_valuationSubring_iff, ← Valuation.mem_integer_iff]; exact ValuationRing.mem_integer_iff B L x
  have hle : B' ≤ A' := fun x hx => by
    obtain ⟨b, rfl⟩ := (hB'mem x).1 hx
    exact (hA'mem _).2 ⟨ψ b, hψL b⟩
  have hne : A' ≠ ⊤ := fun h => by
    have hqinv : (q : L)⁻¹ ∈ A' := h ▸ trivial
    obtain ⟨a, ha⟩ := (hA'mem _).1 hqinv
    apply (IsLocalRing.mem_maximalIdeal _).mp hAq
    refine IsUnit.of_mul_eq_one a (IsFractionRing.injective A L ?_)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hq.ne_zero)]
  let f : B →+* B' := (algebraMap B L).codRestrict B'.toSubring (fun b => (hB'mem _).2 ⟨b, rfl⟩)
  have hf : Function.Surjective f := fun y => by
    obtain ⟨b, hb⟩ := (hB'mem _).1 y.2
    exact ⟨b, Subtype.ext hb⟩
  haveI : IsPrincipalIdealRing B' := IsPrincipalIdealRing.of_surjective f hf
  haveI : Ring.KrullDimLE 1 B' := inferInstance
  have hAB : B' = A' := ValuationSubring.eq_of_le_of_ne_top B' hle hne
  have hψsurj : Function.Surjective ψ := fun a => by
    have ha : algebraMap A L a ∈ B' := hAB ▸ (hA'mem _).2 ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := (hB'mem _).1 ha
    exact ⟨b, IsFractionRing.injective A L (by rw [hψL, hb])⟩
  have hψinj : Function.Injective ψ := fun x y h =>
    IsFractionRing.injective B L (by rw [← hψL, ← hψL, h])
  let e : B ≃+* A := RingEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  have he_apply : ∀ b : B, e b = ψ b := fun _ => rfl

  have hmax : (IsLocalRing.maximalIdeal B).map ψ = IsLocalRing.maximalIdeal A := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      apply (IsLocalRing.mem_maximalIdeal _).mp hb
      have h' : IsUnit (e.symm (e b)) := (he_apply b ▸ hu).map e.symm
      simpa using h'
    · intro m hm
      obtain ⟨b, rfl⟩ := hψsurj m
      have hb : b ∈ IsLocalRing.maximalIdeal B := by
        rw [IsLocalRing.mem_maximalIdeal] at hm ⊢
        exact fun hu => hm (hu.map ψ)
      exact Ideal.mem_map_of_mem ψ hb

  have hqA : Ideal.span {(q : A)} = Ideal.span {ϖ ^ (q - 1)} := by
    have h := congrArg (Ideal.map ψ) hqB
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_pow, hmax, hϖ,
      Ideal.span_singleton_pow] at h
    exact h
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hqA
  exact ⟨u, u.isUnit, by rw [← hu, mul_comm]⟩

end S_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing
end P2MW
export P2MW.S_IsCyclotomicExtension_exists_isUnit_pow_sub_one_eq_mul_natCast_of_isDiscreteValuationRing (solution)
