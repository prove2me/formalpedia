-- Prove2me | solution 1 for N25.unitRelationClearedSeries25_coefficients_of_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:51:05.931498+00:00
-- url     : https://prove2.me/submissions/5be22f70-ecaf-4ede-98df-7bff5b8d3307

import Definitions.Def_N25_UnitRelation
import Definitions.Def_N25_UnitRelationCertificate
import Theorems.Thm_N25_etaResidueSeries25_trunc_prefix
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_unitRelationClearedSeries25_factorization

set_option autoImplicit false

open scoped BigOperators

open Polynomial

namespace N25

private theorem map_numerator {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (q p r s : A) :
    f (unitRelationNumerator25 q p r s) =
      unitRelationNumerator25 (f q) (f p) (f r) (f s) := by
  simp only [unitRelationNumerator25, map_sub, map_add, map_mul, map_pow, map_ofNat]

private theorem pairPolynomial_coe (t a b : ℕ) :
    (unitPairPolynomial25 t a b : PowerSeries ℤ) =
      (∏ m ∈ Finset.range t,
        ((1 - PowerSeries.X^(25*m+a)) *
          (1 - PowerSeries.X^(25*(m+1)-a)) : PowerSeries ℤ)) *
      (∏ m ∈ Finset.range t,
        ((1 - PowerSeries.X^(25*m+b)) *
          (1 - PowerSeries.X^(25*(m+1)-b)) : PowerSeries ℤ)) := by
  let ι : ℤ[X] →+* PowerSeries ℤ := Polynomial.coeToPowerSeries.ringHom
  have hpoly : unitPairPolynomial25 t a b =
      (∏ m ∈ Finset.range t,
        ((1 - Polynomial.X^(25*m+a)) *
          (1 - Polynomial.X^(25*(m+1)-a)) : ℤ[X])) *
      (∏ m ∈ Finset.range t,
        ((1 - Polynomial.X^(25*m+b)) *
          (1 - Polynomial.X^(25*(m+1)-b)) : ℤ[X])) := by
    unfold unitPairPolynomial25 Polynomial.binomialBlocksPolynomial unitPairBlocks25
    simp only [List.map_map, Function.comp_def, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one]
    rw [← List.prod_toFinset _ (List.nodup_range (n := t))]
    simp only [List.toFinset_range]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro m _
    ring
  change ι (unitPairPolynomial25 t a b) = _
  rw [hpoly, map_mul, map_prod, map_prod]
  simp only [map_mul, map_sub, map_one, map_pow]
  simp only [ι, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

/-- A finite numerator coefficient certificate transfers to the original
cleared integral series, using the invertible residue-pair denominators. -/
theorem _root_.solution (N t : ℕ)
    (hNt : N ≤ 25*t)
    (hp : ∀ n : ℕ, n < N → (unitRelationNumeratorPolynomial25 t).coeff n = 0) :
    ∀ n : ℕ, n < N → PowerSeries.coeff n unitRelationClearedSeries25 = 0 := by
  let I : Ideal (PowerSeries ℤ) := Ideal.span {PowerSeries.X^N}
  let φ : PowerSeries ℤ →+* (PowerSeries ℤ ⧸ I) := Ideal.Quotient.mk I
  have equal_of_trunc (p q : PowerSeries ℤ) (h : PowerSeries.trunc N p = PowerSeries.trunc N q) :
      φ p = φ q := by
    apply Ideal.Quotient.eq.mpr
    change p-q ∈ Ideal.span {PowerSeries.X^N}
    rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hc := congrArg (Polynomial.coeff · n) h
    simp only [PowerSeries.coeff_trunc, if_pos hn] at hc
    simpa only [map_sub, sub_eq_zero] using hc
  have pair_map (a b : ℕ) (ha : 0<a) (ha25 : a<25) (hb : 0<b) (hb25 : b<25) :
      φ (etaResidueSeries25 a * etaResidueSeries25 b) =
        φ (unitPairPolynomial25 t a b : PowerSeries ℤ) := by
    rw [pairPolynomial_coe, map_mul, map_mul]
    rw [equal_of_trunc _ _ (etaResidueSeries25_trunc_prefix a N t ha ha25 hNt),
      equal_of_trunc _ _ (etaResidueSeries25_trunc_prefix b N t hb hb25 hNt)]
  have hzero : φ (unitRelationNumeratorPolynomial25 t : PowerSeries ℤ) = 0 := by
    rw [← map_zero φ]
    apply equal_of_trunc
    apply Polynomial.ext
    intro n
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with hn
    · simpa only [Polynomial.coeff_coe, map_zero] using hp n hn
    · rfl
  have hnum : φ (unitRelationNumerator25 PowerSeries.X
      (unitPairSeries25 0) (unitPairSeries25 1) (unitPairSeries25 2)) = 0 := by
    have h₀ := pair_map 1 7 (by omega) (by omega) (by omega) (by omega)
    have h₁ := pair_map 2 11 (by omega) (by omega) (by omega) (by omega)
    have h₂ := pair_map 3 4 (by omega) (by omega) (by omega) (by omega)
    change φ (unitPairSeries25 0) = _ at h₀
    change φ (unitPairSeries25 1) = _ at h₁
    change φ (unitPairSeries25 2) = _ at h₂
    rw [map_numerator, h₀, h₁, h₂]
    have hpoly : φ (unitRelationNumeratorPolynomial25 t : PowerSeries ℤ) =
        unitRelationNumerator25 (φ PowerSeries.X)
          (φ (unitPairPolynomial25 t 1 7 : PowerSeries ℤ))
          (φ (unitPairPolynomial25 t 2 11 : PowerSeries ℤ))
          (φ (unitPairPolynomial25 t 3 4 : PowerSeries ℤ)) := by
      let ι : ℤ[X] →+* PowerSeries ℤ := Polynomial.coeToPowerSeries.ringHom
      change φ (ι (unitRelationNumeratorPolynomial25 t)) = _
      rw [unitRelationNumeratorPolynomial25, map_numerator ι, map_numerator φ]
      simp only [ι, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
    exact hpoly.symm.trans hzero
  have hfactor := congrArg φ unitRelationClearedSeries25_factorization.1
  simp only [map_mul, hnum, mul_zero] at hfactor
  have hu := unitRelationClearedSeries25_factorization.2.map φ
  obtain ⟨u, hu⟩ := hu
  rw [map_mul] at hu
  rw [← hu] at hfactor
  have hz : φ unitRelationClearedSeries25 = 0 := by
    calc
      _ = (φ unitRelationClearedSeries25 * (u : PowerSeries ℤ ⧸ I)) * ↑u⁻¹ := by
        simp [mul_assoc]
      _ = 0 := by rw [hfactor, zero_mul]
  have hmem := (Ideal.Quotient.eq_zero_iff_mem).mp hz
  change unitRelationClearedSeries25 ∈ Ideal.span {PowerSeries.X^N} at hmem
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at hmem
  exact hmem

end N25
