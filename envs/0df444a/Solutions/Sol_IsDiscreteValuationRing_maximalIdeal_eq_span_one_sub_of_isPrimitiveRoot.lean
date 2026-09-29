-- Prove2me | solution 1 for IsDiscreteValuationRing.maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/8cae2880-d98b-5047-9d5d-22c784db367f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot

set_option autoImplicit false

namespace Maxid

open IsLocalRing

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

end Maxid
p2m_reactivate "P2MW.S_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot.Maxid"

theorem solution
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (z : A) (hz : algebraMap A L z = ζ) :
    IsLocalRing.maximalIdeal A = Ideal.span {1 - z} := by
  classical
  haveI : NumberField L := IsCyclotomicExtension.numberField {p} ℚ L
  have hp : (p : ℕ).Prime := Fact.out

  set O := NumberField.RingOfIntegers L
  set φ : O →+* A := Maxid.emb A with hφdef
  have hφ : ∀ x : O, algebraMap A L (φ x) = (x : L) := Maxid.algebraMap_emb A
  set π : O := hζ.toInteger - 1 with hπdef
  have hπL : (π : L) = ζ - 1 := by simp [hπdef, IsPrimitiveRoot.toInteger]
  have hφπ : φ π = z - 1 := IsFractionRing.injective A L (by rw [hφ, map_sub, hz, map_one, hπL])
  have hπ0 : π ≠ 0 := fun h => hζ.ne_one hp.one_lt (by
    have h' : (π : L) = 0 := by rw [h]; rfl
    rwa [hπL, sub_eq_zero] at h')

  set Q : Ideal O := (IsLocalRing.maximalIdeal A).comap φ with hQdef
  haveI hQprime : Q.IsPrime := Ideal.comap_isPrime φ _
  have hpQ : (p : O) ∈ Q := by
    rw [hQdef, Ideal.mem_comap, map_natCast]; exact hAp
  haveI hQover : Q.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff, Ideal.under_def]
    refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) Ideal.IsPrime.ne_top' ?_
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
    exact hpQ
  have hQ : Q = Ideal.span {π} := IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p L hζ Q

  have hmem : 1 - z ∈ IsLocalRing.maximalIdeal A := by
    have h1 : π ∈ Q := hQ ▸ Ideal.mem_span_singleton_self π
    rw [hQdef, Ideal.mem_comap, hφπ] at h1
    simpa using (IsLocalRing.maximalIdeal A).neg_mem h1

  have hunit : ∀ s : O, s ∉ Q → IsUnit (φ s) := fun s hs => by
    by_contra h
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr h)

  have hQbot : Q ≠ ⊥ := by
    rw [hQ]; exact (Submodule.ne_bot_iff _).mpr ⟨π, Ideal.mem_span_singleton_self π, hπ0⟩
  let B := Localization.AtPrime Q
  haveI : IsDiscreteValuationRing B := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hQbot B
  have hinjOL : Function.Injective (algebraMap O L) := IsFractionRing.injective O L
  have hunitL : ∀ s : Q.primeCompl, IsUnit (algebraMap O L s) := fun s =>
    isUnit_iff_ne_zero.mpr (fun h => s.2 (by
      have hs0 : (s : O) = 0 := hinjOL (by rw [h, map_zero])
      rw [hs0]; exact Q.zero_mem))
  letI algBL : Algebra B L := (IsLocalization.lift (M := Q.primeCompl) (S := B) (g := algebraMap O L) hunitL).toAlgebra
  haveI : IsScalarTower O B L := IsScalarTower.of_algebraMap_eq (fun x =>
    (IsLocalization.lift_eq (M := Q.primeCompl) (S := B) (g := algebraMap O L) hunitL x).symm)
  haveI : IsFractionRing B L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl B L
  let ψ : B →+* A := IsLocalization.lift (M := Q.primeCompl) (S := B) (g := φ) (fun s => hunit s s.2)
  have hψ : ∀ x : O, ψ (algebraMap O B x) = φ x := fun x => IsLocalization.lift_eq _ x
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
    have hpinv : (p : L)⁻¹ ∈ A' := h ▸ trivial
    obtain ⟨a, ha⟩ := (hA'mem _).1 hpinv
    apply (IsLocalRing.mem_maximalIdeal _).mp hAp
    refine IsUnit.of_mul_eq_one a (IsFractionRing.injective A L ?_)
    rw [map_mul, ha, map_natCast, map_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero)]

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

  apply le_antisymm
  · intro m hm
    obtain ⟨b, rfl⟩ := hψsurj m
    have hb : b ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal] at hm ⊢
      exact fun hu => hm (hu.map ψ)
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q B] at hb
    have hb' := Ideal.map_mono hQ.le hb
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hb'
    obtain ⟨c, rfl⟩ := hb'
    rw [map_mul, hψ, hφπ, Ideal.mem_span_singleton]
    exact ⟨-ψ c, by ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact hmem

end S_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot
end P2MW
export P2MW.S_IsDiscreteValuationRing_maximalIdeal_eq_span_one_sub_of_isPrimitiveRoot (solution)
