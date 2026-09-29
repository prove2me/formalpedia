-- Prove2me | solution 1 for IsCyclotomicExtension.Rat.algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/04efda1b-4a1b-5b11-9326-1f5f78c05a44

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP

set_option autoImplicit false

open scoped Pointwise NumberField

namespace KummerUnram

section Transport
variable {K K' : Type*} [Field K] [Field K']

theorem mem_nonunits_comap_iff (A : ValuationSubring K') (φ : K →+* K') (x : K) :
    x ∈ (A.comap φ).nonunits ↔ φ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero_iff φ φ.injective,
    ← map_inv₀, ValuationSubring.mem_comap]

theorem inv_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (h : x ∉ A.nonunits) : x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
  exact h.2

theorem ne_top_of_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A.nonunits) (hx0 : x ≠ 0) : A ≠ ⊤ := by
  intro h
  rw [ValuationSubring.mem_nonunits_iff_or] at hx
  rcases hx with hx | hx
  · exact hx0 hx
  · apply hx; rw [h]; trivial

theorem mem_nonunits_of_mem_of_not_isUnit (A : ValuationSubring K) {x : K} (hx : x ∈ A) (h : ¬ IsUnit (⟨x, hx⟩ : A)) :
    x ∈ A.nonunits :=
  ValuationSubring.coe_mem_nonunits_iff.mpr h

theorem nonunits_mul_mem (A : ValuationSubring K) {x y : K} (hx : x ∈ A.nonunits) (hy : y ∈ A) : x * y ∈ A.nonunits := by
  have hxA : x ∈ A := A.nonunits_le hx
  have h1 : (⟨x, hxA⟩ : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hx
  have h2 := Ideal.mul_mem_right (⟨y, hy⟩ : A) _ h1
  exact ValuationSubring.coe_mem_nonunits_iff.mpr h2

theorem not_mem_nonunits_of_inv_mem (A : ValuationSubring K) {x : K} (hx0 : x ≠ 0) (hxi : x⁻¹ ∈ A) : x ∉ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not]
  exact ⟨hx0, hxi⟩

theorem valuation_eq_one_of_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A) (hxn : x ∉ A.nonunits) :
    A.valuation x = 1 :=
  le_antisymm ((A.valuation_le_one_iff x).mpr hx) (not_lt.mp (fun h => hxn (A.mem_nonunits_iff.mpr h)))

end Transport
end KummerUnram

namespace InertiaSurj

open IsCyclotomicExtension NumberField

section Cyclotomic

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [CharZero M] [IsCyclotomicExtension {p} ℚ M]

theorem exists_sub_eq_mul (τ : M ≃ₐ[ℚ] M) (y : M) (hy : y ∈ Algebra.adjoin ℤ ({zeta p ℚ M} : Set M)) :
    ∃ c ∈ Algebra.adjoin ℤ ({zeta p ℚ M} : Set M), τ y - y = (zeta p ℚ M - 1) * c := by
  set ζ := zeta p ℚ M with hζdef
  have hζ : IsPrimitiveRoot ζ p := zeta_spec p ℚ M

  have hτζ : ∃ m : ℕ, τ ζ = ζ ^ m := by
    have h1 : (τ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    exact ⟨i, hi.symm⟩
  obtain ⟨m, hm⟩ := hτζ

  have hτS : ∀ z ∈ Algebra.adjoin ℤ ({ζ} : Set M), τ z ∈ Algebra.adjoin ℤ ({ζ} : Set M) := by
    intro z hz
    have : (τ : M →+* M).toIntAlgHom z ∈ (Algebra.adjoin ℤ ({ζ} : Set M)).map (τ : M →+* M).toIntAlgHom := ⟨z, hz, rfl⟩
    rw [AlgHom.map_adjoin, Set.image_singleton] at this
    have hle : Algebra.adjoin ℤ {(τ : M →+* M).toIntAlgHom ζ} ≤ Algebra.adjoin ℤ ({ζ} : Set M) := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      show τ ζ ∈ Algebra.adjoin ℤ ({ζ} : Set M)
      rw [hm]; exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) _
    exact hle this
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx

      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · exfalso
        rw [h0, pow_zero] at hm
        have : ζ = 1 := τ.injective (by rw [hm, map_one])
        exact hζ.ne_one hp.out.one_lt this
      · refine ⟨ζ * (Finset.range (m - 1)).sum (fun i => ζ ^ i), ?_, ?_⟩
        · exact Subalgebra.mul_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ)
            (Subalgebra.sum_mem _ fun i _ => Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton ℤ ζ) _)
        · rw [hm]
          have h := geom_sum_mul ζ (m - 1)
          calc ζ ^ m - ζ = ζ * (ζ ^ (m - 1) - 1) := by
                  rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hpos]
            _ = (ζ - 1) * (ζ * (Finset.range (m - 1)).sum (fun i => ζ ^ i)) := by rw [← h]; ring
  | algebraMap r => exact ⟨0, Subalgebra.zero_mem _, by simp⟩
  | add x y hx hy ihx ihy =>
      obtain ⟨c, hc, hcx⟩ := ihx
      obtain ⟨d, hd, hdy⟩ := ihy
      exact ⟨c + d, Subalgebra.add_mem _ hc hd, by rw [map_add, mul_add, ← hcx, ← hdy]; ring⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨c, hc, hcx⟩ := ihx
      obtain ⟨d, hd, hdy⟩ := ihy
      refine ⟨τ x * d + c * y, Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hτS x hx) hd) (Subalgebra.mul_mem _ hc hy), ?_⟩
      have : τ (x * y) - x * y = τ x * (τ y - y) + (τ x - x) * y := by rw [map_mul]; ring
      rw [this, hcx, hdy]; ring

theorem exists_sub_eq_mul_of_isIntegral (τ : M ≃ₐ[ℚ] M) (a : M) (ha : IsIntegral ℤ a) :
    ∃ c : M, IsIntegral ℤ c ∧ τ a - a = (zeta p ℚ M - 1) * c := by
  haveI := Rat.isIntegralClosure_adjoin_singleton_of_prime (K := M) (zeta_spec p ℚ M)
  have hmem : a ∈ Algebra.adjoin ℤ ({zeta p ℚ M} : Set M) := by
    obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ ({zeta p ℚ M} : Set M))).mp ha
    rw [← hy]; exact y.2
  obtain ⟨c, hc, h⟩ := exists_sub_eq_mul τ a hmem
  refine ⟨c, ?_, h⟩
  exact (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ ({zeta p ℚ M} : Set M)) (R := ℤ) (B := M)).mpr ⟨⟨c, hc⟩, rfl⟩

end Cyclotomic

end InertiaSurj

namespace InertiaSurj

open IsCyclotomicExtension NumberField

section Val

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [CharZero M] [IsCyclotomicExtension {p} ℚ M] [NumberField M]

theorem mem_of_isIntegral (B : ValuationSubring M) {a : M} (ha : IsIntegral ℤ a) : a ∈ B := by
  have h : IsIntegral B a := ha.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [← hy]; exact y.2

noncomputable def toB (B : ValuationSubring M) : 𝓞 M →+* B :=
  ((algebraMap (𝓞 M) M)).codRestrict B.toSubring (fun a => mem_of_isIntegral B a.isIntegral_coe)

@[scoped simp] theorem coe_toB (B : ValuationSubring M) (a : 𝓞 M) : ((toB B a : B) : M) = (a : M) := rfl

variable (B : ValuationSubring M) (hB : (p : M) ∈ B.nonunits)
include hB

theorem comap_maximalIdeal_eq :
    (IsLocalRing.maximalIdeal B).comap (toB B) = Ideal.span {(zeta_spec p ℚ M).toInteger - 1} := by
  set P := (IsLocalRing.maximalIdeal B).comap (toB B) with hP
  haveI hPp : P.IsPrime := Ideal.comap_isPrime _ _
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have hpP : (p : ℤ) ∈ P.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, hP, Ideal.mem_comap]
      apply ValuationSubring.coe_mem_nonunits_iff.mp
      simpa using hB
    haveI : (P.under ℤ).IsPrime := Ideal.IsPrime.under ℤ P
    have hprime : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hprime.isMaximal (by simp [hp.out.ne_zero])
    exact ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ((Ideal.span_singleton_le_iff_mem _).mpr hpP)⟩
  exact Rat.eq_span_zeta_sub_one_of_liesOver' p M (zeta_spec p ℚ M) P

theorem not_mem_nonunits_iff (a : 𝓞 M) :
    (a : M) ∉ B.nonunits ↔ a ∉ Ideal.span {(zeta_spec p ℚ M).toInteger - 1} := by
  rw [← comap_maximalIdeal_eq B hB, Ideal.mem_comap, not_iff_not]
  show ((toB B a : B) : M) ∈ B.nonunits ↔ _
  exact ValuationSubring.coe_mem_nonunits_iff

theorem zeta_sub_one_mem_nonunits : zeta p ℚ M - 1 ∈ B.nonunits := by
  have h : (zeta_spec p ℚ M).toInteger - 1 ∈ (IsLocalRing.maximalIdeal B).comap (toB B) := by
    rw [comap_maximalIdeal_eq B hB]; exact Ideal.subset_span rfl
  rw [Ideal.mem_comap] at h
  have := ValuationSubring.coe_mem_nonunits_iff.mpr h
  simpa using this

theorem sub_mem_nonunits (τ : M ≃ₐ[ℚ] M) (a : M) (ha : IsIntegral ℤ a) : τ a - a ∈ B.nonunits := by
  obtain ⟨c, hc, h⟩ := exists_sub_eq_mul_of_isIntegral (p := p) τ a ha
  rw [h]
  exact KummerUnram.nonunits_mul_mem B (zeta_sub_one_mem_nonunits B hB) (mem_of_isIntegral B hc)

theorem map_not_mem_nonunits (τ : M ≃ₐ[ℚ] M) (a : M) (ha : IsIntegral ℤ a) (hna : a ∉ B.nonunits) : τ a ∉ B.nonunits := by
  intro h
  apply hna
  have : a = τ a - (τ a - a) := by ring
  rw [this]
  exact B.nonunits.sub_mem h (sub_mem_nonunits B hB τ a ha)

theorem exists_eq_div (x : M) (hx : x ∈ B) :
    ∃ a s : 𝓞 M, (s : M) ∉ B.nonunits ∧ x = (a : M) * ((s : M))⁻¹ := by
  classical
  set 𝔭 : Ideal (𝓞 M) := Ideal.span {(zeta_spec p ℚ M).toInteger - 1} with h𝔭
  haveI : 𝔭.IsPrime := by rw [h𝔭]; exact Rat.isPrime_span_zeta_sub_one' (hζ := zeta_spec p ℚ M)
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    rw [h𝔭, Ne, Ideal.span_singleton_eq_bot, sub_eq_zero]
    intro h
    apply (zeta_spec p ℚ M).ne_one hp.out.one_lt
    have := congrArg (fun x : 𝓞 M => (x : M)) h
    simpa using this
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 M) := ⟨𝔭, inferInstance, h𝔭ne⟩
  have hp0 : (p : M) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hBtop : B ≠ ⊤ := KummerUnram.ne_top_of_mem_nonunits B hB hp0
  have hle : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w ≤ B := by
    rintro y ⟨a, s, hs, rfl⟩
    have hsn : ((s : 𝓞 M) : M) ∉ B.nonunits := (not_mem_nonunits_iff B hB s).mpr hs
    exact B.mul_mem _ _ (mem_of_isIntegral B a.isIntegral_coe) (KummerUnram.inv_mem_of_not_mem_nonunits B hsn)
  have hVB : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w = B :=
    ValuationSubring.eq_of_le_of_ne_top _ hle hBtop
  have hx' : x ∈ IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M w := by rw [hVB]; exact hx
  obtain ⟨a, s, hs, rfl⟩ := hx'
  exact ⟨a, s, (not_mem_nonunits_iff B hB s).mpr hs, rfl⟩

end Val

end InertiaSurj
p2m_reactivate "P2MW.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP.InertiaSurj"

namespace InertiaSurj

open IsCyclotomicExtension NumberField

section Inertia

variable {p : ℕ} [hp : Fact p.Prime] {M : Type*} [Field M] [CharZero M] [IsCyclotomicExtension {p} ℚ M] [NumberField M]
variable (B : ValuationSubring M) (hB : (p : M) ∈ B.nonunits)
include hB

theorem map_mem (τ : M ≃ₐ[ℚ] M) (x : M) (hx : x ∈ B) : τ x ∈ B := by
  obtain ⟨a, s, hs, rfl⟩ := exists_eq_div B hB x hx
  rw [map_mul, map_inv₀]
  have hτa : IsIntegral ℤ (τ (a : M)) := a.isIntegral_coe.map τ
  have hτs : τ (s : M) ∉ B.nonunits := map_not_mem_nonunits B hB τ s s.isIntegral_coe hs
  exact B.mul_mem _ _ (mem_of_isIntegral B hτa) (KummerUnram.inv_mem_of_not_mem_nonunits B hτs)

theorem smul_eq (τ : M ≃ₐ[ℚ] M) : τ • B = B := by
  apply le_antisymm
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx
    have := map_mem B hB τ _ hx
    simpa using this
  · intro x hx
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact map_mem B hB τ⁻¹ x hx

theorem smul_sub_mem_nonunits (τ : M ≃ₐ[ℚ] M) (x : M) (hx : x ∈ B) : τ x - x ∈ B.nonunits := by
  obtain ⟨a, s, hs, rfl⟩ := exists_eq_div B hB x hx
  have hs0 : (s : M) ≠ 0 := fun h => hs (by rw [h]; exact B.nonunits.zero_mem)
  have hτs : τ (s : M) ∉ B.nonunits := map_not_mem_nonunits B hB τ s s.isIntegral_coe hs
  have hτs0 : τ (s : M) ≠ 0 := fun h => hτs (by rw [h]; exact B.nonunits.zero_mem)

  have key : τ ((a : M) * ((s : M))⁻¹) - (a : M) * ((s : M))⁻¹ =
      (τ (a : M) - a) * (τ (s : M))⁻¹ - ((a : M) * ((s : M))⁻¹) * ((τ (s : M) - s) * (τ (s : M))⁻¹) := by
    rw [map_mul, map_inv₀]
    field_simp
    ring
  rw [key]
  apply B.nonunits.sub_mem
  · exact KummerUnram.nonunits_mul_mem B (sub_mem_nonunits B hB τ a a.isIntegral_coe)
      (KummerUnram.inv_mem_of_not_mem_nonunits B hτs)
  · have h1 : (τ (s : M) - s) * (τ (s : M))⁻¹ ∈ B.nonunits :=
      KummerUnram.nonunits_mul_mem B (sub_mem_nonunits B hB τ s s.isIntegral_coe)
        (KummerUnram.inv_mem_of_not_mem_nonunits B hτs)
    rw [mul_comm]
    exact KummerUnram.nonunits_mul_mem B h1 hx

end Inertia
p2m_reactivate "P2MW.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP.InertiaSurj"

end InertiaSurj
p2m_reactivate "P2MW.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP.InertiaSurj"

theorem solution
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (k : Type) [Field k] [CharP k p] [Algebra A k]
    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a)) :
    ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A k (s • a) = algebraMap A k a := by
  classical
  intro s a
  haveI : NumberField L := IsCyclotomicExtension.numberField {p} ℚ L
  have hp : p.Prime := Fact.out
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have hp0A : (p : A) ≠ 0 := fun h => by
    have : (p : L) = 0 := by rw [← map_natCast (algebraMap A L), h, map_zero]
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) this

  haveI : ValuationRing A := inferInstance
  let B : ValuationSubring L :=
    { (algebraMap A L).range with
      mem_or_inv_mem' := fun x => by
        rcases (ValuationRing.iff_isInteger_or_isInteger A L).mp inferInstance x with h | h
        · exact Or.inl h
        · exact Or.inr h }
  have hBmem : ∀ x : L, x ∈ B ↔ ∃ b : A, algebraMap A L b = x := fun x => Iff.rfl
  have hBunit : ∀ b : A, (algebraMap A L b) ∉ B.nonunits → IsUnit b := by
    intro b hb
    rw [ValuationSubring.mem_nonunits_iff_or, not_or] at hb
    obtain ⟨h0, hinv⟩ := hb
    rw [not_not, hBmem] at hinv
    obtain ⟨c, hc⟩ := hinv
    refine IsUnit.of_mul_eq_one c (hinj ?_)
    rw [map_mul, hc, map_one, mul_inv_cancel₀ h0]
  have hB : ((p : ℕ) : L) ∈ B.nonunits := by
    by_contra h
    have hu := hBunit p (by rwa [map_natCast])
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hAp) hu

  have hxa : algebraMap A L a ∈ B := (hBmem _).mpr ⟨a, rfl⟩
  have hnon : s (algebraMap A L a) - algebraMap A L a ∈ B.nonunits := InertiaSurj.smul_sub_mem_nonunits (p := p) B hB s _ hxa
  have hmax : s • a - a ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : algebraMap A L (s • a - a) ∉ B.nonunits := by
      intro hn
      obtain ⟨u, hu'⟩ := hu
      have h1 : algebraMap A L (s • a - a) ≠ 0 := by
        rw [map_ne_zero_iff _ hinj, ← hu']; exact u.ne_zero
      rw [ValuationSubring.mem_nonunits_iff_or] at hn
      rcases hn with hn | hn
      · exact h1 hn
      · apply hn
        rw [hBmem]
        refine ⟨↑u⁻¹, ?_⟩
        rw [← hu']
        symm
        apply inv_eq_of_mul_eq_one_right
        rw [← map_mul, Units.mul_inv, map_one]
    apply this
    rw [map_sub, hΓA]
    exact hnon

  have hker : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A k) := by
    have hpk : (p : A) ∈ RingHom.ker (algebraMap A k) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    haveI : (RingHom.ker (algebraMap A k)).IsPrime := RingHom.ker_isPrime _
    have hne : RingHom.ker (algebraMap A k) ≠ ⊥ := fun h => hp0A (by rw [h, Ideal.mem_bot] at hpk; exact hpk)
    have hm : (RingHom.ker (algebraMap A k)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hm).symm
  have h := hker hmax
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h
  exact h

end S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP
end P2MW
export P2MW.S_IsCyclotomicExtension_Rat_algebraMap_smul_eq_algebraMap_of_isDiscreteValuationRing_of_charP (solution)
