-- Prove2me | solution 1 for ModularCurve.FullLevel.AuxLevel.exists_unramified_subDVR_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/29a5a631-f2c0-561c-86a2-977bd14e422d

import Mathlib
import Theorems.Thm_Algebra_adjoin_isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
import Theorems.Thm_IsRegularLocalRing_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_unramified_subDVR_adjoin_eq_top

set_option autoImplicit false

namespace UnrSubDVR

open IsLocalRing Polynomial

theorem isUnit_intCast_of_not_dvd {A : Type*} [CommRing A] [IsLocalRing A] (q : ℕ) (hq : q.Prime)
    (hAq : (q : A) ∈ maximalIdeal A) (y : ℤ) (hy : ¬ (q : ℤ) ∣ y) : IsUnit ((y : ℤ) : A) := by
  have hcop : IsCoprime (q : ℤ) y := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).mpr hy
  obtain ⟨a, b, hab⟩ := hcop
  by_contra hnu
  have hy𝔪 : ((y : ℤ) : A) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hnu
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have := congrArg (Int.cast : ℤ → A) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hAq) (Ideal.mul_mem_left _ _ hy𝔪)
  exact (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

theorem exists_subDVR (q ℓ : ℕ) [hq : Fact q.Prime] [hl : Fact ℓ.Prime] (hqℓ : q ≠ ℓ)
    (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CharZero A]
    (hAq : (q : A) ∈ maximalIdeal A) (ω : A) (hω : IsPrimitiveRoot ω ℓ) :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀) (_ : Algebra A₀ A),
      maximalIdeal A₀ = Ideal.span {(q : A₀)} ∧ Finite (ResidueField A₀) ∧
      Function.Injective (algebraMap A₀ A) ∧
      (∃ ω₀ : A₀, IsPrimitiveRoot ω₀ ℓ ∧ algebraMap A₀ A ω₀ = ω) := by
  classical
  have hqp : q.Prime := hq.out
  have hlp : ℓ.Prime := hl.out

  haveI h𝓆p : (Ideal.span {(q : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hqp.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hqp
  have h𝓆0 : Ideal.span {(q : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqp.ne_zero
  haveI h𝓆m : (Ideal.span {(q : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal h𝓆p h𝓆0
  haveI : IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {(q : ℤ)})) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ h𝓆0 _
  set O := Localization.AtPrime (Ideal.span {(q : ℤ)}) with hO
  have hMle : (Ideal.span {(q : ℤ)}).primeCompl ≤ nonZeroDivisors ℤ := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero fun h0 => hs (h0 ▸ Ideal.zero_mem _)
  have hℤO : Function.Injective (algebraMap ℤ O) := IsLocalization.injective O hMle

  have hunitA : ∀ y : (Ideal.span {(q : ℤ)}).primeCompl, IsUnit ((Int.castRingHom A) y) := by
    rintro ⟨y, hy⟩
    exact isUnit_intCast_of_not_dvd q hqp hAq y fun hd => hy (Ideal.mem_span_singleton.mpr hd)
  letI : Algebra O A := (IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) hunitA).toAlgebra
  have hφ : ∀ z : ℤ, algebraMap O A (algebraMap ℤ O z) = (z : A) := fun z =>
    IsLocalization.lift_eq (M := (Ideal.span {(q : ℤ)}).primeCompl) hunitA z
  have hφinj : Function.Injective (algebraMap O A) := by
    show Function.Injective (IsLocalization.lift (M := (Ideal.span {(q : ℤ)}).primeCompl) hunitA)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [hℤO.eq_iff]
    exact ⟨fun h => by rw [h], fun h => by exact_mod_cast (Int.cast_inj.mp h : x = y)⟩

  set D : Subalgebra O A := Algebra.adjoin O ({ω} : Set A) with hD
  set P : Ideal D := (maximalIdeal A).comap (algebraMap D A) with hP
  haveI hPp : P.IsPrime := Ideal.IsPrime.comap _
  have hqP : ((q : ℕ) : D) ∈ P := by
    show algebraMap D A (q : D) ∈ maximalIdeal A
    rw [map_natCast]; exact hAq

  have hmon : (cyclotomic ℓ O).Monic := cyclotomic.monic ℓ O
  have hroot : aeval ω (cyclotomic ℓ O) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hω.isRoot_cyclotomic hlp.pos
  have hℓO : ((ℓ : ℕ) : ResidueField O) ≠ 0 := by
    intro h
    rw [← map_natCast (residue O), residue_eq_zero_iff, ← map_natCast (algebraMap ℤ O),
      IsLocalization.AtPrime.to_map_mem_maximal_iff O (Ideal.span {(q : ℤ)}), Ideal.mem_span_singleton] at h
    have := Int.natCast_dvd_natCast.mp h
    exact hqℓ ((Nat.prime_dvd_prime_iff_eq hqp hlp).mp this)
  have hsep : ((cyclotomic ℓ O).map (residue O)).Separable := by
    rw [map_cyclotomic]
    exact (separable_X_pow_sub_C (1 : ResidueField O) hℓO one_ne_zero).of_dvd (cyclotomic.dvd_X_pow_sub_one ℓ _)
  have hmO : maximalIdeal O = (Ideal.span {(q : ℤ)}).map (algebraMap ℤ O) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hmOq : maximalIdeal O = Ideal.span {((q : ℕ) : O)} := by
    rw [hmO, Ideal.map_span, Set.image_singleton, map_natCast]
  have hq𝔪 : (maximalIdeal O).map (algebraMap O D) ≤ P := by
    rw [hmOq, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_le, Set.singleton_subset_iff]
    exact hqP
  obtain ⟨hDVR, h𝔪⟩ :=
    Algebra.adjoin.isDiscreteValuationRing_localization_and_maximalIdeal_eq_of_separable_map
      hφinj ω (cyclotomic ℓ O) hmon hroot hsep P hq𝔪

  have hDinj : Function.Injective (algebraMap D (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl) fun s hs =>
      mem_nonZeroDivisors_of_ne_zero fun h0 => hs (h0 ▸ Ideal.zero_mem _)
  have hunitD : ∀ y : P.primeCompl, IsUnit ((algebraMap D A : D →+* A) y) := by
    rintro ⟨y, hy⟩
    by_contra hnu
    exact hy ((mem_maximalIdeal _).mpr hnu)
  let ψ : Localization.AtPrime P →+* A := IsLocalization.lift (M := P.primeCompl) hunitD
  have hψ : ∀ d : D, ψ (algebraMap D (Localization.AtPrime P) d) = (d : A) := fun d =>
    IsLocalization.lift_eq (M := P.primeCompl) hunitD d
  have hψinj : Function.Injective ψ := by
    show Function.Injective (IsLocalization.lift (M := P.primeCompl) hunitD)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    rw [hDinj.eq_iff]
    exact ⟨fun h => by rw [h], fun h => Subtype.ext h⟩

  have h𝔪q : maximalIdeal (Localization.AtPrime P) = Ideal.span {((q : ℕ) : Localization.AtPrime P)} := by
    rw [h𝔪, hmOq, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.map_span, Set.image_singleton, map_natCast]

  have hfinκ : Finite (ResidueField O) := by
    haveI : Finite (ℤ ⧸ Ideal.span {(q : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod q).symm.toEquiv
    exact Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField (Ideal.span {(q : ℤ)})).surjective
  haveI hDfin : Module.Finite O D :=
    Algebra.finite_adjoin_simple_of_isIntegral ⟨cyclotomic ℓ O, hmon, by rwa [aeval_def] at hroot⟩
  haveI hPover : P.LiesOver (maximalIdeal O) := by
    refine ⟨le_antisymm ?_ ?_⟩
    · exact Ideal.map_le_iff_le_comap.mp hq𝔪 |> fun h => by

        exact ((maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) h).le
    · exact ((maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _))
        (Ideal.map_le_iff_le_comap.mp hq𝔪)).ge
  have hfinDP : Finite (D ⧸ P) := by
    haveI : Finite (O ⧸ maximalIdeal O) := hfinκ
    letI : Algebra (O ⧸ maximalIdeal O) (D ⧸ P) := Ideal.Quotient.algebraOfLiesOver P (maximalIdeal O)
    haveI hmf : Module.Finite (O ⧸ maximalIdeal O) (D ⧸ P) := module_finite_of_liesOver P (maximalIdeal O)
    exact @Module.finite_of_finite (O ⧸ maximalIdeal O) (D ⧸ P) _ _ _ _ hmf
  haveI hPmax : P.IsMaximal := by
    haveI : IsDomain (D ⧸ P) := Ideal.Quotient.isDomain P
    exact Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain (D ⧸ P))
  have hfinA₀ : Finite (ResidueField (Localization.AtPrime P)) :=
    Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField P).surjective
  refine ⟨Localization.AtPrime P, inferInstance, inferInstance, hDVR, ψ.toAlgebra, h𝔪q, hfinA₀, hψinj, ?_⟩
  refine ⟨algebraMap D (Localization.AtPrime P) ⟨ω, Algebra.self_mem_adjoin_singleton O ω⟩, ?_, hψ _⟩
  refine IsPrimitiveRoot.of_map_of_injective (f := ψ) ?_ hψinj
  rw [hψ]; exact hω

end UnrSubDVR

namespace UnrSubDVR

open IsLocalRing Polynomial

section Eisenstein

variable (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : ℕ) [hq : Fact q.Prime]

noncomputable def eis : A₀[X] := ((cyclotomic q ℤ).comp (X + 1)).map (Int.castRingHom A₀)

theorem eis_eq : eis A₀ q = (cyclotomic q A₀).comp (X + 1) := by
  rw [eis, map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one]

theorem eis_monic : (eis A₀ q).Monic := by
  rw [eis_eq]
  exact (cyclotomic.monic q A₀).comp (monic_X_add_C 1) (by rw [← C_1, natDegree_X_add_C]; exact one_ne_zero)

theorem eis_natDegree : (eis A₀ q).natDegree = q - 1 := by
  rw [eis_eq, natDegree_comp, natDegree_cyclotomic, Nat.totient_prime hq.out,
    show (X + 1 : A₀[X]).natDegree = 1 by rw [← C_1, natDegree_X_add_C], mul_one]

theorem eis_coeff_zero : (eis A₀ q).coeff 0 = (q : A₀) := by
  rw [eis_eq, coeff_zero_eq_eval_zero, eval_comp, eval_add, eval_X, eval_one, zero_add, eval_one_cyclotomic_prime]

theorem eis_aeval {S : Type*} [CommRing S] [Algebra A₀ S] (z : S) :
    aeval z (eis A₀ q) = aeval (z + 1) (cyclotomic q A₀) := by
  rw [eis_eq, aeval_comp, aeval_add, aeval_X, map_one]

variable {A₀ q}

theorem eis_isEisensteinAt (h𝔪 : maximalIdeal A₀ = Ideal.span {(q : A₀)}) :
    (eis A₀ q).IsEisensteinAt (maximalIdeal A₀) := by
  refine (eis_monic A₀ q).isEisensteinAt_of_mem_of_notMem (maximalIdeal.isMaximal A₀).ne_top ?_ ?_
  · intro n hn
    rw [eis, coeff_map, h𝔪]
    have hmonℤ : ((cyclotomic q ℤ).comp (X + 1)).Monic :=
      (cyclotomic.monic q ℤ).comp (monic_X_add_C 1) (by rw [← C_1, natDegree_X_add_C]; exact one_ne_zero)
    have hn' : n < ((cyclotomic q ℤ).comp (X + 1)).natDegree := by
      rwa [eis, hmonℤ.natDegree_map] at hn
    have hmem := (cyclotomic_comp_X_add_one_isEisensteinAt q).mem hn'
    rw [Ideal.mem_span_singleton] at hmem ⊢
    obtain ⟨c, hc⟩ := hmem
    refine ⟨(c : A₀), ?_⟩
    rw [hc, map_mul, map_natCast]; rfl
  · rw [eis_coeff_zero, h𝔪, pow_two, Ideal.span_singleton_mul_span_singleton, Ideal.mem_span_singleton]
    rintro ⟨a, ha⟩
    have hq0 : (q : A₀) ≠ 0 := by
      intro h0
      have : maximalIdeal A₀ = ⊥ := by rw [h𝔪, h0, Ideal.span_singleton_eq_bot]
      exact (IsDiscreteValuationRing.not_isField A₀) (isField_iff_maximalIdeal_eq.mpr this)
    have h1 : (q : A₀) * (1 - q * a) = 0 := by linear_combination ha
    rcases mul_eq_zero.mp h1 with h | h
    · exact hq0 h
    · have hu : IsUnit (q : A₀) := isUnit_iff_exists_inv.mpr ⟨a, by linear_combination (-1 : A₀) * h⟩
      exact (maximalIdeal.isMaximal A₀).ne_top (Ideal.eq_top_of_isUnit_mem _ (h𝔪 ▸ Ideal.mem_span_singleton_self _) hu)

theorem eis_prime (h𝔪 : maximalIdeal A₀ = Ideal.span {(q : A₀)}) : Prime (eis A₀ q) := by
  have hirr := (eis_isEisensteinAt h𝔪).irreducible (maximalIdeal.isMaximal A₀).isPrime (eis_monic A₀ q).isPrimitive
    (by rw [eis_natDegree]; have := hq.out.two_le; omega)
  exact hirr.prime

theorem isDiscreteValuationRing_adjoinRoot_eis (h𝔪 : maximalIdeal A₀ = Ideal.span {(q : A₀)}) :
    ∃ (_ : IsDomain (AdjoinRoot (eis A₀ q))), IsDiscreteValuationRing (AdjoinRoot (eis A₀ q)) := by
  haveI hdom : IsDomain (AdjoinRoot (eis A₀ q)) := AdjoinRoot.isDomain_of_prime (eis_prime h𝔪)
  refine ⟨hdom, ?_⟩
  have hq2 := hq.out.two_le
  have hE := eis_isEisensteinAt h𝔪
  obtain ⟨hreg, hdim⟩ := IsRegularLocalRing.adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_of_coeff_zero_not_mem_sq
    A₀ (eis A₀ q) (eis_monic A₀ q) (by rw [eis_natDegree]; omega) (fun i hi => hE.mem hi) hE.notMem
  have hnf : ¬ IsField A₀ := IsDiscreteValuationRing.not_isField A₀
  have hdimA₀ : ringKrullDim A₀ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one A₀ hnf
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace (AdjoinRoot (eis A₀ q))).mp hreg
  rw [hdim, hdimA₀] at hcot
  have hcot1 : Module.finrank (ResidueField (AdjoinRoot (eis A₀ q))) (CotangentSpace (AdjoinRoot (eis A₀ q))) = 1 := by
    exact_mod_cast hcot
  have hnfB : ¬ IsField (AdjoinRoot (eis A₀ q)) := by
    intro hF
    have h0 := (finrank_cotangentSpace_eq_zero_iff (R := AdjoinRoot (eis A₀ q))).mpr hF
    omega
  exact ((IsDiscreteValuationRing.TFAE (AdjoinRoot (eis A₀ q)) hnfB).out 5 0).mp hcot1

end Eisenstein

section Transport

theorem mem_range_of_mul_mem_range {B A : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing A] [IsDomain A] [IsLocalRing A] (φ : B →+* A) (hφ : Function.Injective φ)
    (t : B) (ht0 : t ≠ 0) (ht : φ t ∈ maximalIdeal A)
    (x : A) (c y : B) (hc : c ≠ 0) (hy : φ y = φ c * x) : x ∈ Set.range φ := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B

  have hπA : φ π ∈ maximalIdeal A := by
    obtain ⟨e, u, hte⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ht0 hπ
    have he : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one] at hte
      have : IsUnit (φ t) := hte ▸ (u.isUnit.map φ)
      exact (mem_maximalIdeal _).mp ht this
    have : φ π ^ e ∈ maximalIdeal A := by
      have h1 : φ t = φ ↑u * φ π ^ e := by rw [hte, map_mul, map_pow]
      have h2 : φ π ^ e = φ ↑(u⁻¹) * φ t := by
        rw [h1, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      rw [h2]; exact Ideal.mul_mem_left _ _ ht
    exact (maximalIdeal.isMaximal A).isPrime.mem_of_pow_mem e this
  by_cases hx : x = 0
  · exact ⟨0, by rw [map_zero, hx]⟩
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy
    exact hx ((mul_eq_zero.mp hy.symm).resolve_left ((map_ne_zero_iff φ hφ).mpr hc))
  obtain ⟨m, u, hcm⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hπ
  obtain ⟨n, v, hyn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have hφπ0 : φ π ≠ 0 := (map_ne_zero_iff φ hφ).mpr hπ.ne_zero
  rcases Nat.lt_or_ge n m with hmn | hmn
  swap
  · obtain ⟨k, rfl⟩ : ∃ k, n = m + k := ⟨n - m, by omega⟩
    refine ⟨↑v * ↑u⁻¹ * π ^ k, ?_⟩
    have huu : (u : B) * ↑u⁻¹ = 1 := Units.mul_inv u
    have : φ c * x = φ c * φ (↑v * ↑u⁻¹ * π ^ k) := by
      rw [← hy, hyn, hcm, ← map_mul]
      congr 1
      rw [pow_add]
      linear_combination (-((v : B) * π ^ m * π ^ k)) * huu
    exact (mul_left_cancel₀ ((map_ne_zero_iff φ hφ).mpr hc) this).symm
  · exfalso
    apply (mem_maximalIdeal _).mp hπA

    have h1 : φ π ^ n * (φ ↑u * φ π ^ (m - n) * x) = φ π ^ n * φ ↑v := by
      have := hy
      rw [hyn, hcm, map_mul, map_mul, map_pow, map_pow, show m = n + (m - n) by omega, pow_add] at this
      linear_combination (-1 : A) * this
    have h2 := mul_left_cancel₀ (pow_ne_zero n hφπ0) h1
    have hvu : IsUnit (φ ↑v) := v.isUnit.map φ
    rw [← h2] at hvu
    have h3 : IsUnit (φ π ^ (m - n)) := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hvu)
    exact (isUnit_pow_iff (by omega)).mp h3

theorem sub_one_mem_maximalIdeal_of_pow_eq_one {A : Type*} [CommRing A] [IsLocalRing A] (q : ℕ) (hq : q.Prime)
    (hAq : (q : A) ∈ maximalIdeal A) (z : A) (hz : z ^ q = 1) : z - 1 ∈ maximalIdeal A := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hchar : CharP (ResidueField A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]; rw [← map_natCast (residue A), residue_eq_zero_iff]; exact hAq
  rw [← residue_eq_zero_iff, map_sub, map_one]
  have h : (residue A z - 1) ^ q = 0 := by
    rw [sub_pow_char, ← map_pow, hz, map_one, one_pow, sub_self]
  exact pow_eq_zero_iff hq.ne_zero |>.mp h

end Transport

end UnrSubDVR

namespace UnrSubDVR

open IsLocalRing Polynomial

theorem exists_int_mul_mem_adjoin (n : ℕ) [NeZero n]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {n} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [Algebra A L] (hinj : Function.Injective (algebraMap A L))
    (μ : A) (hμ : IsPrimitiveRoot μ n) (x : A) :
    ∃ b : ℤ, b ≠ 0 ∧ (b : A) * x ∈ Algebra.adjoin ℤ ({μ} : Set A) := by
  classical
  have hμL : IsPrimitiveRoot (algebraMap A L μ) n := hμ.map_of_injective hinj
  have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) (B := L) hμL
  have hx : algebraMap A L x ∈ Algebra.adjoin ℚ ({algebraMap A L μ} : Set L) := by rw [htop]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (S := ℚ) p
  set P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (S := ℚ) p with hP
  refine ⟨(b : ℤ), nonZeroDivisors.coe_ne_zero b, ?_⟩
  have key : algebraMap A L (aeval μ P) = algebraMap A L ((b : ℤ) * x) := by
    rw [← aeval_algebraMap_apply, ← aeval_map_algebraMap ℚ, hb]
    change aeval (algebraMap A L μ) ((b : ℤ) • p) = _
    have hp' : aeval (algebraMap A L μ) p = algebraMap A L x := hp
    rw [map_zsmul, hp', map_mul, map_intCast, zsmul_eq_mul]
  rw [← hinj key]
  exact Polynomial.aeval_mem_adjoin_singleton ℤ μ

end UnrSubDVR

open IsLocalRing Polynomial UnrSubDVR in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (ζA : A) (hζA : algebraMap A L ζA = ζ)
    (K : Type) [CommRing K] [Algebra A K] :
    ∃ (A₀ : Type) (_ : CommRing A₀) (_ : IsDomain A₀) (_ : IsDiscreteValuationRing A₀)
      (_ : Algebra A₀ A) (_ : Algebra A₀ K) (_ : IsScalarTower A₀ A K),
      IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)} ∧
      Finite (IsLocalRing.ResidueField A₀) ∧
      Function.Injective (algebraMap A₀ A) ∧ Module.Finite A₀ A ∧
      IsUnit ((ℓ : ℕ) : A₀) ∧ IsUnit ((M' : ℕ) : A₀) ∧ IsUnit (2 : A₀) ∧ IsUnit (3 : A₀) ∧
      (∃ ω : A₀, IsPrimitiveRoot ω ℓ) ∧
      Algebra.adjoin A₀ {ζA} = ⊤ := by
  classical
  have hqp : q.Prime := Fact.out
  have hlp : ℓ.Prime := Fact.out
  haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero hqp.ne_zero hlp.ne_zero⟩
  have hinjAL : Function.Injective (algebraMap A L) := IsFractionRing.injective A L
  haveI : CharZero A := RingHom.charZero (algebraMap A L)
  have hζA' : IsPrimitiveRoot ζA q := IsPrimitiveRoot.of_map_of_injective (by rw [hζA]; exact hζ) hinjAL

  have hμL := IsCyclotomicExtension.zeta_spec (q * ℓ) ℚ L
  have hωL : IsPrimitiveRoot ((IsCyclotomicExtension.zeta (q * ℓ) ℚ L) ^ q) ℓ :=
    hμL.pow (Nat.pos_of_ne_zero (NeZero.ne _)) rfl
  obtain ⟨ω, hωeq⟩ : ∃ ω : A, algebraMap A L ω = (IsCyclotomicExtension.zeta (q * ℓ) ℚ L) ^ q := by
    refine IsIntegrallyClosed.algebraMap_eq_of_integral ⟨X ^ ℓ - 1, monic_X_pow_sub_C 1 hlp.ne_zero, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_one, hωL.pow_eq_one, sub_self]
  have hω : IsPrimitiveRoot ω ℓ := IsPrimitiveRoot.of_map_of_injective (by rw [hωeq]; exact hωL) hinjAL

  obtain ⟨A₀, _, _, _, _, h𝔪, hfin, hinj0, ω₀, hω₀, hω₀eq⟩ := exists_subDVR q ℓ hℓq.symm A hAq ω hω

  obtain ⟨_, hBdvr⟩ := isDiscreteValuationRing_adjoinRoot_eis (A₀ := A₀) (q := q) h𝔪
  have hζroot : aeval (ζA - 1) (eis A₀ q) = 0 := by
    rw [eis_aeval, sub_add_cancel, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζA'.isRoot_cyclotomic hqp.pos
  have hζroot' : (eis A₀ q).eval₂ (Algebra.ofId A₀ A) (ζA - 1) = 0 := by
    simpa [Polynomial.aeval_def] using hζroot
  set φₐ : AdjoinRoot (eis A₀ q) →ₐ[A₀] A := AdjoinRoot.liftAlgHom (eis A₀ q) (Algebra.ofId A₀ A) (ζA - 1) hζroot' with hφₐ
  have hφroot : φₐ (AdjoinRoot.root (eis A₀ q)) = ζA - 1 := by rw [hφₐ, AdjoinRoot.liftAlgHom_root]
  have hφalg : ∀ a : A₀, φₐ (algebraMap A₀ _ a) = algebraMap A₀ A a := fun a => φₐ.commutes a
  haveI hBfin : Module.Finite A₀ (AdjoinRoot (eis A₀ q)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' (eis_monic A₀ q)).basis
  have hφinj : Function.Injective φₐ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := A₀)
    rw [← le_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap A₀ A a = 0 := by rw [← hφalg]; exact ha
    rw [Ideal.mem_bot]
    exact hinj0 (by rw [this, map_zero])

  set φ : AdjoinRoot (eis A₀ q) →+* A := φₐ.toRingHom with hφ
  have hφinj' : Function.Injective φ := hφinj
  have hμ : IsPrimitiveRoot (ζA * ω) (q * ℓ) := by
    rw [IsPrimitiveRoot.iff_orderOf, (Commute.all ζA ω).orderOf_mul_eq_mul_orderOf_of_coprime]
    · rw [← hζA'.eq_orderOf, ← hω.eq_orderOf]
    · rw [← hζA'.eq_orderOf, ← hω.eq_orderOf]
      exact (Nat.coprime_primes hqp hlp).mpr hℓq.symm
  have hμmem : ζA * ω ∈ φ.range := by
    refine ⟨(AdjoinRoot.root (eis A₀ q) + 1) * algebraMap A₀ _ ω₀, ?_⟩
    rw [hφ, map_mul, map_add, map_one]
    show (φₐ (AdjoinRoot.root (eis A₀ q)) + 1) * φₐ (algebraMap A₀ _ ω₀) = ζA * ω
    rw [hφroot, hφalg, hω₀eq, sub_add_cancel]
  have hrange : ∀ z ∈ Algebra.adjoin ℤ ({ζA * ω} : Set A), z ∈ Set.range φ := by
    intro z hz
    have hle : Algebra.adjoin ℤ ({ζA * ω} : Set A) ≤ (φ.toIntAlgHom).range :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (by obtain ⟨y, hy⟩ := hμmem; exact ⟨y, hy⟩))
    obtain ⟨y, hy⟩ := hle hz
    exact ⟨y, hy⟩
  have hA : ∀ x : A, x ∈ Set.range φ := by
    intro x
    obtain ⟨b, hb0, hbx⟩ := exists_int_mul_mem_adjoin (q * ℓ) L A hinjAL (ζA * ω) hμ x
    obtain ⟨y, hy⟩ := hrange _ hbx
    refine mem_range_of_mul_mem_range φ hφinj' (q : AdjoinRoot (eis A₀ q)) ?_ ?_ x (b : AdjoinRoot (eis A₀ q)) y ?_ ?_
    · intro h
      have := congrArg φ h
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.mpr hqp.ne_zero) this
    · rw [map_natCast]; exact hAq
    · intro h
      have := congrArg φ h
      rw [map_intCast, map_zero] at this
      exact (Int.cast_ne_zero.mpr hb0) this
    · rw [hy, map_intCast]
  have hφsurj : Function.Surjective φₐ := fun x => hA x

  have hunit : ∀ n : ℕ, ¬ q ∣ n → IsUnit ((n : ℕ) : A₀) := by
    intro n hn
    by_contra hnu
    have hmem : ((n : ℕ) : A₀) ∈ maximalIdeal A₀ := (mem_maximalIdeal _).mpr hnu
    rw [h𝔪, Ideal.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    have hnA : IsUnit ((n : ℤ) : A) := isUnit_intCast_of_not_dvd q hqp hAq n (by exact_mod_cast hn)
    apply (mem_maximalIdeal _).mp ?_ hnA
    have := congrArg (algebraMap A₀ A) ha
    rw [map_natCast, map_mul, map_natCast] at this
    rw [Int.cast_natCast, this]
    exact Ideal.mul_mem_right _ _ hAq
  letI algK : Algebra A₀ K := ((algebraMap A K).comp (algebraMap A₀ A)).toAlgebra
  haveI : IsScalarTower A₀ A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨A₀, inferInstance, inferInstance, inferInstance, inferInstance, algK, inferInstance, h𝔪, hfin, hinj0,
    Module.Finite.of_surjective φₐ.toLinearMap hφsurj, hunit ℓ ?_, hunit M' hqM', ?_, ?_, ⟨ω₀, hω₀⟩, ?_⟩
  · intro h; exact hℓq ((Nat.prime_dvd_prime_iff_eq hqp hlp).mp h).symm
  · exact_mod_cast hunit 2 (fun h => by have := Nat.le_of_dvd two_pos h; omega)
  · exact_mod_cast hunit 3 (fun h => by have := Nat.le_of_dvd (by norm_num) h; omega)
  ·
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hφsurj x
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
    rw [hφₐ, AdjoinRoot.liftAlgHom_mk, Algebra.toRingHom_ofId, ← aeval_def]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr
      (Subalgebra.sub_mem _ (Algebra.self_mem_adjoin_singleton A₀ ζA) (Subalgebra.one_mem _)))
      (Polynomial.aeval_mem_adjoin_singleton A₀ _)

end S_ModularCurve_FullLevel_AuxLevel_exists_unramified_subDVR_adjoin_eq_top
end P2MW
export P2MW.S_ModularCurve_FullLevel_AuxLevel_exists_unramified_subDVR_adjoin_eq_top (solution)
