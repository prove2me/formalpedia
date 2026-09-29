-- Prove2me | solution 1 for IsCyclotomicExtension.Padic.isIntegralClosure_adjoin_singleton_of_prime_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5a708c67-3e39-551d-957b-bf0a27d38f7d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow

set_option autoImplicit false

noncomputable section

namespace TP9D

open Polynomial Algebra

variable (p : ℕ) [Fact p.Prime]

lemma isEisensteinAt_padicInt (k : ℕ) :
    (((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p])).IsEisensteinAt
      (Ideal.span {(p : ℤ_[p])}) := by
  have hp : p.Prime := Fact.out
  set g : ℤ[X] := (cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1) with hg
  have hZ : g.IsEisensteinAt (Ideal.span {(p : ℤ)}) :=
    cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p k
  have hgm : g.Monic := by
    have : (X + 1 : ℤ[X]) = X + C 1 := by rw [C_1]
    rw [hg, this]
    exact (cyclotomic.monic _ ℤ).comp_X_add_C 1
  have hg'm : (g.map (Int.castRingHom ℤ_[p])).Monic := hgm.map _
  have hdeg : (g.map (Int.castRingHom ℤ_[p])).natDegree = g.natDegree := hgm.natDegree_map _
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr PadicInt.prime_p
  refine hg'm.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
  · intro n hn
    rw [hdeg] at hn
    rw [Polynomial.coeff_map, Ideal.mem_span_singleton]
    have h1 := hZ.mem hn
    rw [Ideal.mem_span_singleton] at h1
    exact map_dvd (Int.castRingHom ℤ_[p]) h1
  · intro hmem
    apply hZ.notMem
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem ⊢
    rw [Polynomial.coeff_map, eq_intCast] at hmem
    exact_mod_cast (PadicInt.pow_p_dvd_int_iff 2 (g.coeff 0)).mp hmem

lemma map_cyclotomic_comp (k : ℕ) :
    ((cyclotomic (p ^ (k + 1)) ℤ).comp (X + 1)).map (Int.castRingHom ℤ_[p]) =
      (cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1) := by
  rw [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one]

lemma monic_cyclotomic_comp (k : ℕ) : ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).Monic := by
  have : (X + 1 : ℤ_[p][X]) = X + C 1 := by rw [C_1]
  rw [this]
  exact (cyclotomic.monic _ ℤ_[p]).comp_X_add_C 1

lemma irreducible_cyclotomic (k : ℕ) : Irreducible (cyclotomic (p ^ (k + 1)) ℚ_[p]) := by
  have hp : p.Prime := Fact.out
  have hE := isEisensteinAt_padicInt p k
  rw [map_cyclotomic_comp] at hE
  have hmon := monic_cyclotomic_comp p k
  have hprime : (Ideal.span {(p : ℤ_[p])}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr PadicInt.prime_p
  have hdeg : 0 < ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)).natDegree := by
    rw [natDegree_comp, natDegree_cyclotomic]
    have : (X + 1 : ℤ_[p][X]).natDegree = 1 := by
      have : (X + 1 : ℤ_[p][X]) = X + C 1 := by rw [C_1]
      rw [this, natDegree_X_add_C]
    rw [this, mul_one]
    exact Nat.totient_pos.mpr (pow_pos hp.pos _)
  have hirrZ : Irreducible ((cyclotomic (p ^ (k + 1)) ℤ_[p]).comp (X + 1)) :=
    hE.irreducible hprime hmon.isPrimitive hdeg
  have hirrQ : Irreducible ((cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1)) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ℚ_[p])).mp hirrZ
    rwa [Polynomial.map_comp, map_cyclotomic, Polynomial.map_add, map_X, Polynomial.map_one] at h

  have hcomp : (algEquivAevalXAddC (1 : ℚ_[p])) (cyclotomic (p ^ (k + 1)) ℚ_[p]) =
      (cyclotomic (p ^ (k + 1)) ℚ_[p]).comp (X + 1) := by
    simp [algEquivAevalXAddC, comp_eq_aeval]
  rw [← hcomp] at hirrQ
  exact (MulEquiv.irreducible_iff (algEquivAevalXAddC (1 : ℚ_[p])).toMulEquiv).mp hirrQ

lemma irreducible_cyclotomic' (k : ℕ) : Irreducible (cyclotomic (p ^ k) ℚ_[p]) := by
  cases k with
  | zero =>
    rw [pow_zero, cyclotomic_one]
    exact irreducible_X_sub_C 1
  | succ k => exact irreducible_cyclotomic p k

section Main

variable (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]

omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] in
lemma adjoin_singleton_eq_adjoin_sub_one (ζ : K) :
    Algebra.adjoin ℤ_[p] ({ζ} : Set K) = Algebra.adjoin ℤ_[p] ({ζ - 1} : Set K) := by
  apply le_antisymm
  · refine adjoin_le ?_
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    have hmem := Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ_[p] (ζ - 1))
      (Subalgebra.one_mem (Algebra.adjoin ℤ_[p] ({ζ - 1} : Set K)))
    rwa [sub_add_cancel] at hmem
  · refine adjoin_le ?_
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ_[p] _) (Subalgebra.one_mem _)

theorem mem_adjoin_of_isIntegral (k : ℕ) [hcycl : IsCyclotomicExtension {p ^ k} ℚ_[p] K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k)) {x : K} (h : IsIntegral ℤ_[p] x) :
    x ∈ Algebra.adjoin ℤ_[p] ({ζ} : Set K) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  haveI := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ_[p] K
  haveI : Algebra.IsSeparable ℚ_[p] K := Algebra.IsSeparable.of_integral ℚ_[p] K
  have hirr : Irreducible (cyclotomic (p ^ k) ℚ_[p]) := irreducible_cyclotomic' p k
  have hζint : IsIntegral ℤ_[p] ζ := (hζ.isIntegral (NeZero.pos _)).tower_top

  let B := hζ.powerBasis ℚ_[p]
  have hBgen : B.gen = ζ := IsPrimitiveRoot.powerBasis_gen ℚ_[p] hζ
  have hint : IsIntegral ℤ_[p] B.gen := by rw [hBgen]; exact hζint
  have H₀ := discr_mul_isIntegral_mem_adjoin ℚ_[p] hint h
  obtain ⟨u, n, hun⟩ := IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow hζ hirr
  rw [hun, hBgen] at H₀
  have H : ((p : ℚ_[p]) ^ n) • x ∈ Algebra.adjoin ℤ_[p] ({ζ} : Set K) := by
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa using H₀
    · have H₁ := Subalgebra.neg_mem _ H₀
      rw [← neg_smul] at H₁
      convert H₁ using 2
      push_cast
      ring

  have H' : ((p : ℤ_[p]) ^ n) • x ∈ Algebra.adjoin ℤ_[p] ({ζ - 1} : Set K) := by
    rw [← adjoin_singleton_eq_adjoin_sub_one]
    have : ((p : ℤ_[p]) ^ n) • x = ((p : ℚ_[p]) ^ n) • x := by
      rw [← IsScalarTower.algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ n) x, map_pow, map_natCast]
    rw [this]
    exact H

  cases k with
  | zero =>
    haveI : IsCyclotomicExtension {1} ℚ_[p] K := by simpa using hcycl
    have hx : x ∈ (⊥ : Subalgebra ℚ_[p] K) := by
      rw [IsCyclotomicExtension.singleton_one ℚ_[p] K]
      exact Algebra.mem_top
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.1 hx
    replace h := (isIntegral_algebraMap_iff (algebraMap ℚ_[p] K).injective).1 h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hz, ← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ _
  | succ k =>
    let B' := hζ.subOnePowerBasis ℚ_[p]
    have hB'gen : B'.gen = ζ - 1 := IsPrimitiveRoot.subOnePowerBasis_gen ℚ_[p] hζ
    have hint' : IsIntegral ℤ_[p] B'.gen := by rw [hB'gen]; exact hζint.sub isIntegral_one
    have hmin : (minpoly ℤ_[p] B'.gen).IsEisensteinAt (Submodule.span ℤ_[p] {(p : ℤ_[p])}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hint'
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp hirr
      rw [hB'gen] at h₁ ⊢
      rw [h₁, ← map_cyclotomic (p ^ (k + 1)) (algebraMap ℤ_[p] ℚ_[p]),
        show (X + 1 : ℚ_[p][X]) = map (algebraMap ℤ_[p] ℚ_[p]) (X + 1) by simp, ← map_comp] at h₂
      have h₃ := map_injective (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p]) h₂
      rw [h₃, ← map_cyclotomic_comp]
      exact isEisensteinAt_padicInt p k
    have hmem := mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (R := ℤ_[p])
      (K := ℚ_[p]) (B := B') PadicInt.prime_p hint' h (by rw [hB'gen]; exact H') hmin
    rw [hB'gen] at hmem
    rwa [adjoin_singleton_eq_adjoin_sub_one]

theorem main (k : ℕ) [IsCyclotomicExtension {p ^ k} ℚ_[p] K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set K)) ℤ_[p] K := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.ne_zero⟩
  refine ⟨Subtype.val_injective, fun {x} => ⟨fun h => ⟨⟨x, mem_adjoin_of_isIntegral p K k hζ h⟩,
    rfl⟩, ?_⟩⟩
  rintro ⟨y, rfl⟩
  have hζint : IsIntegral ℤ_[p] ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  exact IsIntegral.algebraMap
    ((le_integralClosure_iff_isIntegral.1 (adjoin_le_integralClosure hζint)).isIntegral _)

end Main

end TP9D

end

theorem solution (p : ℕ) [Fact p.Prime] (k : ℕ) (K : Type*) [Field K] [Algebra ℚ_[p] K]
    [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [IsCyclotomicExtension {p ^ k} ℚ_[p] K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    IsIntegralClosure (Algebra.adjoin ℤ_[p] ({ζ} : Set K)) ℤ_[p] K :=
  TP9D.main p K k hζ

end S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow
end P2MW
export P2MW.S_IsCyclotomicExtension_Padic_isIntegralClosure_adjoin_singleton_of_prime_pow (solution)
