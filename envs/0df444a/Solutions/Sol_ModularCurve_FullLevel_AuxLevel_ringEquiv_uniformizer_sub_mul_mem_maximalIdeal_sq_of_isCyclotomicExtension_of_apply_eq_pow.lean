-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/e8996385-fd3d-5e97-be02-e76ee1253535

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow

set_option autoImplicit false

namespace CycUnit

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero

theorem le_exp_neg_one_of_lt_one {x : ℤᵐ⁰} (hx0 : x ≠ 0) (hx : x < 1) : x ≤ exp (-1 : ℤ) := by
  rw [← exp_log hx0] at hx ⊢
  rw [← exp_zero, exp_lt_exp] at hx
  rw [exp_le_exp]
  omega

theorem maximalIdeal_eq_span_one_sub
    (q : ℕ) [hq : Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (z : A) (hz : algebraMap A L z = ζ) :
    IsLocalRing.maximalIdeal A = Ideal.span {1 - z} := by
  classical
  haveI : NumberField L := IsCyclotomicExtension.numberField {q * ℓ} ℚ L
  have hqp : q.Prime := hq.out
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L

  let A' : ValuationSubring L := ValuationSubring.ofSubring (algebraMap A L).range (by
    intro x
    rcases ValuationRing.isInteger_or_isInteger A x with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩)
  have memA' : ∀ x : L, x ∈ A' ↔ ∃ a : A, algebraMap A L a = x := fun x =>
    ValuationSubring.mem_ofSubring _ _ x
  have hq0 : (q : L) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hqinv : (q : L)⁻¹ ∉ A' := by
    intro h
    obtain ⟨a, ha⟩ := (memA' _).mp h
    have hqa : (q : A) * a = 1 := hinj (by rw [map_mul, map_one, ha, map_natCast, mul_inv_cancel₀ hq0])
    exact (IsLocalRing.mem_maximalIdeal _).mp hAq (isUnit_iff_exists_inv.mpr ⟨a, hqa⟩)
  have hA'top : A' ≠ ⊤ := by
    intro h
    apply hqinv
    rw [h]
    exact ValuationSubring.mem_top _

  have hOA' : ∀ x : 𝓞 L, algebraMap (𝓞 L) L x ∈ A' := by
    intro x
    have hint : IsIntegral A (algebraMap (𝓞 L) L x) := (RingOfIntegers.isIntegral_coe x).tower_top
    exact (memA' _).mpr (((isIntegrallyClosed_iff L).mp inferInstance) hint)
  let φ : 𝓞 L →+* A' := (algebraMap (𝓞 L) L).codRestrict A' hOA'
  have hφ : ∀ x : 𝓞 L, ((φ x : A') : L) = algebraMap (𝓞 L) L x := fun x => rfl

  let 𝔓 : Ideal (𝓞 L) := Ideal.comap φ (IsLocalRing.maximalIdeal A')
  haveI h𝔓prime : 𝔓.IsPrime := Ideal.IsPrime.comap φ

  have hqO : ((q : ℕ) : 𝓞 L) ∈ 𝔓 := by
    change φ q ∈ IsLocalRing.maximalIdeal A'
    rw [ValuationSubring.valuation_lt_one_iff]
    have h1 : ¬ A'.valuation ((q : L)⁻¹) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff]; exact hqinv
    have h2 : ((φ q : A') : L) = (q : L) := by rw [hφ, map_natCast]
    rw [h2]
    rw [map_inv₀, not_le, one_lt_inv_iff₀] at h1
    · exact h1.2
  have h𝔓ne : 𝔓 ≠ ⊥ := by
    intro h
    have : ((q : ℕ) : 𝓞 L) = 0 := by rw [h] at hqO; exact hqO
    exact hqp.ne_zero (by exact_mod_cast this)
  let v : HeightOneSpectrum (𝓞 L) := ⟨𝔓, h𝔓prime, h𝔓ne⟩

  have hle : valuationSubringAtPrime L v ≤ A' := by
    intro x hx
    change x ∈ (valuationSubringAtPrime L v).toSubring at hx
    rw [valuationSubringAtPrime_toSubring] at hx
    obtain ⟨a, s, hs, rfl⟩ := hx

    have hsA : IsUnit (φ s) := by
      by_contra hns
      exact hs ((IsLocalRing.mem_maximalIdeal _).mpr hns)
    have hsinv : (algebraMap (𝓞 L) L s)⁻¹ ∈ A' := by
      obtain ⟨u, hu⟩ := hsA
      have hmul : ((u : A') : L) * ((u⁻¹ : A'ˣ) : A') = 1 := by
        rw [← A'.coe_mul]
        simp
      have : (algebraMap (𝓞 L) L s)⁻¹ = ((u⁻¹ : A'ˣ) : A') := by
        rw [← hφ s, ← hu]
        exact (eq_inv_of_mul_eq_one_right hmul).symm ▸ rfl
      rw [this]
      exact ((u⁻¹ : A'ˣ) : A').2
    exact A'.mul_mem _ _ (hOA' a) hsinv
  have hA'eq : A' = (v.valuation L).valuationSubring := by
    rw [← valuationSubringAtPrime_eq_valuationSubring]
    exact (ValuationSubring.eq_of_le_of_ne_top _ hle hA'top).symm
  have memv : ∀ x : L, (v.valuation L x ≤ 1 ↔ ∃ a : A, algebraMap A L a = x) := by
    intro x
    rw [← memA', hA'eq, Valuation.mem_valuationSubring_iff]

  have hunit : ∀ a : A, IsUnit a ↔ v.valuation L (algebraMap A L a) = 1 := by
    intro a
    constructor
    · intro hu
      obtain ⟨b, hb⟩ := hu.exists_right_inv
      have ha1 : v.valuation L (algebraMap A L a) ≤ 1 := (memv _).mpr ⟨a, rfl⟩
      have hb1 : v.valuation L (algebraMap A L b) ≤ 1 := (memv _).mpr ⟨b, rfl⟩
      have hab : 1 ≤ v.valuation L (algebraMap A L b) * v.valuation L (algebraMap A L a) := by
        rw [← map_mul, ← map_mul, mul_comm, hb, map_one, map_one]
      exact eq_one_of_one_le_mul_right hb1 ha1 hab
    · intro h1
      have ha0 : algebraMap A L a ≠ 0 := by
        intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
      have : v.valuation L (algebraMap A L a)⁻¹ ≤ 1 := by rw [map_inv₀, h1, inv_one]
      obtain ⟨b, hb⟩ := (memv _).mp this
      have hab : a * b = 1 := hinj (by rw [map_mul, hb, map_one, mul_inv_cancel₀ ha0])
      exact isUnit_iff_exists_inv.mpr ⟨b, hab⟩
  have hmax : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A ↔ v.valuation L (algebraMap A L a) < 1 := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    have ha1 : v.valuation L (algebraMap A L a) ≤ 1 := (memv _).mpr ⟨a, rfl⟩
    exact ⟨fun h => lt_of_le_of_ne ha1 h, fun h => h.ne⟩

  haveI : 𝔓.LiesOver (Ideal.span {((q : ℕ) : ℤ)}) := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    refine (Int.ideal_span_isMaximal_of_prime q).eq_of_le (Ideal.IsPrime.comap _).ne_top ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 L) (q : ℤ) ∈ 𝔓
    rw [map_natCast]; exact hqO
  have hram : (Ideal.span {((q : ℕ) : ℤ)}).ramificationIdx' 𝔓 = q - 1 := by
    have hqℓ : ¬ q ∣ ℓ := fun h => hℓq ((Nat.prime_dvd_prime_iff_eq hqp (Fact.out)).mp h).symm
    have := IsCyclotomicExtension.Rat.ramificationIdx_eq (q * ℓ) (m := ℓ) (p := q) (k := 0) L 𝔓
      (by ring) hqℓ
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (by simpa using hqp.ne_zero)]
    simpa using this
  have hmapq : Ideal.map (algebraMap ℤ (𝓞 L)) (Ideal.span {((q : ℕ) : ℤ)}) = Ideal.span {((q : ℕ) : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hqO0 : ((q : ℕ) : 𝓞 L) ≠ 0 := by exact_mod_cast hqp.ne_zero
  have hvq : v.valuation L (q : L) = exp (-((q - 1 : ℕ) : ℤ)) := by
    have : (q : L) = algebraMap (𝓞 L) L ((q : ℕ) : 𝓞 L) := by rw [map_natCast]
    rw [this, valuation_of_algebraMap, intValuation_eq_exp_neg_multiplicity v hqO0]
    congr 2
    have hmul := Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity
      (p := Ideal.span {((q : ℕ) : ℤ)}) (P := 𝔓) (by rw [hmapq]; exact mt Ideal.span_singleton_eq_bot.mp hqO0) h𝔓prime
    rw [hmapq] at hmul
    rw [← hram, hmul]

  have hζA' : v.valuation L ζ ≤ 1 := (memv _).mpr ⟨z, hz⟩
  have hpow_le : ∀ (μ : L), v.valuation L μ ≤ 1 → ∀ n : ℕ, v.valuation L (1 - μ ^ n) ≤ v.valuation L (1 - μ) := by
    intro μ hμ n
    rw [← mul_neg_geom_sum, map_mul]
    apply mul_le_of_le_one_right'
    apply Valuation.map_sum_le
    intro i _
    rw [map_pow]; exact pow_le_one' hμ _
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  have hfac : ∀ μ ∈ primitiveRoots q L, v.valuation L (1 - μ) = v.valuation L (1 - ζ) := by
    intro μ hμ
    rw [mem_primitiveRoots hqp.pos] at hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
    apply le_antisymm (hpow_le ζ hζA' i)
    have hμ1 : v.valuation L (ζ ^ i) ≤ 1 := by rw [map_pow]; exact pow_le_one' hζA' _
    have := hpow_le (ζ ^ i) hμ1 j
    rwa [hj] at this
  have hprod : (q : L) = ∏ μ ∈ primitiveRoots q L, (1 - μ) := by
    have h := Polynomial.eval_one_cyclotomic_prime (R := L) (p := q)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
    exact h.symm
  have hζ1 : (1 : L) - ζ ≠ 0 := sub_ne_zero.mpr (hζ.ne_one hqp.one_lt).symm
  have ht0 : v.valuation L (1 - ζ) ≠ 0 := (Valuation.ne_zero_iff _).mpr hζ1
  have hvζ : v.valuation L (1 - ζ) = exp (-1 : ℤ) := by
    have h := congrArg (v.valuation L) hprod
    rw [map_prod, Finset.prod_congr rfl hfac, Finset.prod_const, hζ.card_primitiveRoots,
      Nat.totient_prime hqp, hvq] at h

    rw [← exp_log ht0] at h ⊢
    rw [← exp_nsmul, exp_inj] at h
    rw [exp_inj]
    have hq1 : ((q - 1 : ℕ) : ℤ) ≠ 0 := by
      have := hqp.two_le
      omega
    have : ((q - 1 : ℕ) : ℤ) * (v.valuation L (1 - ζ)).log = ((q - 1 : ℕ) : ℤ) * (-1) := by
      rw [nsmul_eq_mul] at h; linarith
    exact mul_left_cancel₀ hq1 this

  have h1z : algebraMap A L (1 - z) = 1 - ζ := by rw [map_sub, map_one, hz]
  apply le_antisymm
  · intro a ha
    by_cases ha0 : a = 0
    · rw [ha0]; exact Submodule.zero_mem _
    have haL0 : algebraMap A L a ≠ 0 := fun h => ha0 (hinj (by rw [h, map_zero]))
    have hlt := (hmax a).mp ha
    have hle' : v.valuation L (algebraMap A L a) ≤ v.valuation L (1 - ζ) := by
      rw [hvζ]; exact le_exp_neg_one_of_lt_one ((Valuation.ne_zero_iff _).mpr haL0) hlt
    have : v.valuation L (algebraMap A L a / (1 - ζ)) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hle' zero_le'
    obtain ⟨b, hb⟩ := (memv _).mp this
    refine Ideal.mem_span_singleton'.mpr ⟨b, hinj ?_⟩
    rw [map_mul, hb, h1z, div_mul_cancel₀ _ hζ1]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hmax, h1z, hvζ, ← exp_zero, exp_lt_exp]
    norm_num

end CycUnit

open CycUnit in

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (d : (ZMod q)ˣ) (σL : L ≃+* L) (σA : A ≃+* A)
    (hσ : ∀ a : A, algebraMap A L (σA a) = σL (algebraMap A L a))
    (hinert : ∀ a : A, σA a - a ∈ IsLocalRing.maximalIdeal A)
    (hd : σL ζ = ζ ^ ((d : ZMod q).val)) :
    σA ϖ - (((d : ZMod q).val : ℕ) : A) * ϖ ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
  obtain ⟨z, hz⟩ := hζA
  have hinj : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  have key := CycUnit.maximalIdeal_eq_span_one_sub q ℓ hℓq L ζ hζ A hAq z hz
  set dv : ℕ := (d : ZMod q).val with hdv

  have hσz : σA z = z ^ dv := hinj (by rw [hσ, hz, map_pow, hz, hd])
  have hπ : (1 - z) ∈ IsLocalRing.maximalIdeal A := by rw [key]; exact Ideal.mem_span_singleton_self _

  have hS : (∑ i ∈ Finset.range dv, z ^ i) - (dv : A) ∈ IsLocalRing.maximalIdeal A := by
    have : (∑ i ∈ Finset.range dv, z ^ i) - (dv : A) = ∑ i ∈ Finset.range dv, (z ^ i - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [this]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have : z ^ i - 1 = -((1 - z) * ∑ j ∈ Finset.range i, z ^ j) := by rw [mul_neg_geom_sum]; ring
    rw [this]
    exact (IsLocalRing.maximalIdeal A).neg_mem (Ideal.mul_mem_right _ _ hπ)

  have hσπ : σA (1 - z) - (dv : A) * (1 - z) ∈ (IsLocalRing.maximalIdeal A) ^ 2 := by
    have : σA (1 - z) - (dv : A) * (1 - z) = (1 - z) * ((∑ i ∈ Finset.range dv, z ^ i) - (dv : A)) := by
      rw [map_sub, map_one, hσz, ← mul_neg_geom_sum]; ring
    rw [this, pow_two]
    exact Ideal.mul_mem_mul hπ hS

  have hϖmem : ϖ ∈ Ideal.span {1 - z} := by rw [← key, hϖ]; exact Ideal.mem_span_singleton_self _
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hϖmem
  have hw := hinert w
  have : σA (w * (1 - z)) - (dv : A) * (w * (1 - z)) =
      (σA (1 - z) - (dv : A) * (1 - z)) * σA w + (dv : A) * ((1 - z) * (σA w - w)) := by
    rw [map_mul]; ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hσπ) (Ideal.mul_mem_left _ _ ?_)
  rw [pow_two]
  exact Ideal.mul_mem_mul hπ hw

end S_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_ringEquiv_uniformizer_sub_mul_mem_maximalIdeal_sq_of_isCyclotomicExtension_of_apply_eq_pow (solution)
