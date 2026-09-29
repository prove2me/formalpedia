-- Prove2me | solution 1 for ModularCurve.XOneP.exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2f33665b-d375-5d2c-8bab-66078c94047f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension

set_option autoImplicit false

open NumberField

theorem solution
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ) :
    ∀ a : A, ∃ n : ℤ, a - (n : A) ∈ IsLocalRing.maximalIdeal A := by
  classical
  haveI : NumberField L := IsCyclotomicExtension.numberField {p} ℚ L
  have hpr : p.Prime := Fact.out
  set lam : 𝓞 L := hζ.toInteger - 1 with hlam
  have hlam_prime : Prime lam := hζ.zeta_sub_one_prime'
  have hlam0 : lam ≠ 0 := hlam_prime.ne_zero

  have hint : ∀ x : 𝓞 L, ∃ n : ℤ, lam ∣ x - n := by
    intro x
    obtain ⟨f, -, hf⟩ := hζ.integralPowerBasis.exists_eq_aeval x
    rw [IsPrimitiveRoot.integralPowerBasis_gen] at hf
    refine ⟨f.eval 1, ?_⟩
    have h := Polynomial.sub_dvd_eval_sub hζ.toInteger 1 (f.map (Int.castRingHom (𝓞 L)))
    have h1 : Polynomial.eval hζ.toInteger (f.map (Int.castRingHom (𝓞 L))) = x := by
      rw [hf, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]
    have h2 : Polynomial.eval (1 : 𝓞 L) (f.map (Int.castRingHom (𝓞 L))) = ((f.eval 1 : ℤ) : 𝓞 L) := by
      have := Polynomial.eval_intCast_map (Int.castRingHom (𝓞 L)) f 1
      push_cast at this
      rw [this]; rfl
    rwa [h1, h2] at h

  have hex : ∀ x : 𝓞 L, ∃ y : A, algebraMap A L y = (x : L) := fun x =>
    IsIntegrallyClosed.algebraMap_eq_of_integral ((RingOfIntegers.isIntegral x).algebraMap.tower_top (A := A))
  choose φf hφf using hex
  have hinj := IsFractionRing.injective A L
  let φ : 𝓞 L →+* A :=
    { toFun := φf
      map_one' := hinj (by rw [hφf, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [hφf, map_mul, hφf, hφf]; rfl)
      map_zero' := hinj (by rw [hφf, map_zero]; rfl)
      map_add' := fun x y => hinj (by rw [hφf, map_add, hφf, hφf]; rfl) }
  have hφ : ∀ x : 𝓞 L, algebraMap A L (φ x) = (x : L) := hφf

  set π : A := φ lam with hπ
  have hπ0 : π ≠ 0 := by
    intro h
    apply hlam0
    apply RingOfIntegers.coe_injective
    show ((lam : 𝓞 L) : L) = ((0 : 𝓞 L) : L)
    rw [← hφ lam, ← hπ, h, map_zero]; rfl
  have hmne : IsLocalRing.maximalIdeal A ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A) :=
    ⟨⟨0, 1, fun h => hmne (Ideal.Quotient.zero_eq_one_iff.mp h)⟩⟩
  haveI : CharP (A ⧸ IsLocalRing.maximalIdeal A) p := by
    apply ringChar.of_eq
    apply CharP.ringChar_of_prime_eq_zero hpr
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact hAp
  have hπm : π ∈ IsLocalRing.maximalIdeal A := by
    have hzp : (φ hζ.toInteger) ^ p = 1 := hinj (by
      rw [map_pow, hφ, map_one]
      exact hζ.pow_eq_one)
    rw [hπ, hlam, map_sub, map_one, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
    have h1 : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) (φ hζ.toInteger) - 1) ^ p = 0 := by
      rw [sub_pow_char, ← map_pow, hzp, map_one, one_pow, sub_self]
    exact pow_eq_zero_iff hpr.ne_zero |>.mp h1

  have hφm : ∀ y : 𝓞 L, φ y ∈ IsLocalRing.maximalIdeal A ↔ lam ∣ y := by
    have hP : (Ideal.comap φ (IsLocalRing.maximalIdeal A)) = Ideal.span {lam} := by
      haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal A)).IsPrime := Ideal.comap_isPrime φ _
      haveI : (Ideal.comap φ (IsLocalRing.maximalIdeal A)).LiesOver (Ideal.span {(p : ℤ)}) := by
        refine ⟨((Int.ideal_span_isMaximal_of_prime p).eq_of_le ?_ ?_)⟩
        · exact Ideal.IsPrime.ne_top inferInstance
        · rw [Ideal.span_singleton_le_iff_mem]
          show algebraMap ℤ (𝓞 L) p ∈ Ideal.comap φ (IsLocalRing.maximalIdeal A)
          rw [Ideal.mem_comap, eq_intCast, map_intCast, Int.cast_natCast]
          exact hAp
      exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p L hζ _
    intro y
    rw [← Ideal.mem_span_singleton, ← hP, Ideal.mem_comap]
  have hunit : ∀ y : 𝓞 L, ¬ lam ∣ y → IsUnit (φ y) := fun y hy =>
    IsLocalRing.notMem_maximalIdeal.mp (fun h => hy ((hφm y).mp h))
  have hint' : ∀ y : 𝓞 L, ∃ n : ℤ, φ y - n ∈ IsLocalRing.maximalIdeal A := by
    intro y
    obtain ⟨n, hn⟩ := hint y
    refine ⟨n, ?_⟩
    have := (hφm (y - n)).mpr hn
    rwa [map_sub, map_intCast] at this

  intro a
  obtain ⟨x, s, hs, hxs⟩ := IsFractionRing.div_surjective (A := 𝓞 L) (algebraMap A L a)
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  by_cases hx0 : x = 0
  · refine ⟨0, ?_⟩
    have : a = 0 := hinj (by rw [← hxs, hx0, map_zero, zero_div, map_zero])
    rw [this]; simp
  obtain ⟨i, x', hx', rfl⟩ := WfDvdMonoid.max_power_factor hx0 hlam_prime.irreducible
  obtain ⟨j, s', hs', rfl⟩ := WfDvdMonoid.max_power_factor hs0 hlam_prime.irreducible
  have hrel : a * φ (lam ^ j * s') = φ (lam ^ i * x') := by
    apply hinj
    rw [map_mul, hφ, hφ, ← hxs]
    have : ((lam ^ j * s' : 𝓞 L) : L) ≠ 0 := fun h => hs0 (RingOfIntegers.coe_injective (by simpa using h))
    field_simp
  rw [map_mul, map_mul, map_pow, map_pow, ← hπ] at hrel

  have hux := hunit x' hx'
  have hus := hunit s' hs'
  rcases lt_or_ge i j with hij | hij
  ·
    exfalso
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hij
    have h1 : π ^ i * (π ^ (d + 1) * a * φ s') = π ^ i * φ x' := by
      rw [← hrel, hd]; ring
    have h2 := mul_left_cancel₀ (pow_ne_zero i hπ0) h1
    have hπu : IsUnit π := by
      apply isUnit_of_dvd_unit _ (h2 ▸ hux)
      exact Dvd.intro (π ^ d * a * φ s') (by ring)
    exact (IsLocalRing.mem_maximalIdeal _).mp hπm hπu
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    have h1 : π ^ j * (a * φ s') = π ^ j * (π ^ d * φ x') := by
      rw [← mul_assoc, mul_comm (π ^ j) a, mul_assoc, hrel]; ring
    have h2 := mul_left_cancel₀ (pow_ne_zero j hπ0) h1

    rcases Nat.eq_zero_or_pos d with hd | hd
    ·
      subst hd
      rw [pow_zero, one_mul] at h2
      obtain ⟨nx, hnx⟩ := hint' x'
      obtain ⟨ns, hns⟩ := hint' s'

      have hpns : ¬ (p : ℤ) ∣ ns := by
        rintro ⟨t, rfl⟩
        apply (IsLocalRing.mem_maximalIdeal _).mp _ hus
        have : φ s' = (φ s' - ((p : ℤ) * t : ℤ)) + (p : A) * t := by push_cast; ring
        rw [this]
        exact Ideal.add_mem _ hns (Ideal.mul_mem_right _ _ hAp)

      have hns0 : ((ns : ℤ) : ZMod p) ≠ 0 := fun h => hpns ((ZMod.intCast_zmod_eq_zero_iff_dvd ns p).mp h)
      let m : ℤ := ((((ns : ℤ) : ZMod p)⁻¹).val : ℤ)
      have hmcast : ((m : ℤ) : ZMod p) = ((ns : ℤ) : ZMod p)⁻¹ := by
        show (((((ns : ℤ) : ZMod p)⁻¹).val : ℤ) : ZMod p) = _
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      have hmns : (p : ℤ) ∣ 1 - m * ns := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hmcast, inv_mul_cancel₀ hns0, sub_self]
      refine ⟨nx * m, ?_⟩

      have hkey : (a - (nx * m : ℤ)) * φ s' ∈ IsLocalRing.maximalIdeal A := by
        obtain ⟨t, ht⟩ := hmns
        have hpt : ((1 - m * ns : ℤ) : A) ∈ IsLocalRing.maximalIdeal A := by
          rw [ht]; push_cast; exact Ideal.mul_mem_right _ _ hAp
        have : (a - (nx * m : ℤ)) * φ s' =
            (φ x' - nx) - (nx * m : A) * (φ s' - ns) + (nx : A) * ((1 - m * ns : ℤ) : A) := by
          rw [sub_mul, h2]; push_cast; ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.sub_mem _ hnx (Ideal.mul_mem_left _ _ hns)) (Ideal.mul_mem_left _ _ hpt)
      obtain ⟨u, hu⟩ := hus
      have : a - (nx * m : ℤ) = ((a - (nx * m : ℤ)) * φ s') * ↑u⁻¹ := by
        rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [Int.cast_mul] at this ⊢
      rw [this]
      exact Ideal.mul_mem_right _ _ (by exact_mod_cast hkey)
    ·
      refine ⟨0, ?_⟩
      simp only [Int.cast_zero, sub_zero]
      have hmem : a * φ s' ∈ IsLocalRing.maximalIdeal A := by
        rw [h2]
        obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
        rw [pow_succ]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hπm)
      obtain ⟨u, hu⟩ := hus
      have : a = (a * φ s') * ↑u⁻¹ := by rw [← hu, mul_assoc, Units.mul_inv, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end S_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension (solution)
