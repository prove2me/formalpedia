-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/95b2a766-e7a2-50cf-98c5-3f7f966ba2fb

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_KroneckerTransport
import Theorems.Thm_ModularCurve_ModularPolynomialData_natDegree_coeff_le_mul_dedekindPsi_sub_all
import Theorems.Thm_ModularCurve_kroneckerCongruence_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.jqNModC_one"

set_option autoImplicit false

p2m_open "Polynomial ModularCurve~dedekindPsi_prime"

namespace CuspValAlphaK1

theorem dedekindPsi_prime (p : ℕ) [hp : Fact p.Prime] : dedekindPsi p = p + 1 := by
  classical
  have hq : p.Prime := hp.out
  rw [dedekindPsi, Nat.Prime.divisors hq]
  have h1q : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    rw [Finset.mem_singleton]
    exact hq.one_lt.ne
  rw [Finset.filter_insert, if_pos squarefree_one, Finset.filter_singleton, if_pos hq.prime.squarefree,
    Finset.sum_insert h1q, Finset.sum_singleton, Nat.div_one, Nat.div_self hq.pos]

noncomputable def Q (p : ℕ) [NeZero p] (data : ModularPolynomialData p) : Polynomial (Polynomial ℤ) :=
  ∑ k ∈ Finset.range (p + 2), C (reflect (p * (p + 1 - k)) (data.Φ.coeff k)) * X ^ k

theorem coeff_Q (p : ℕ) [NeZero p] (data : ModularPolynomialData p) (k : ℕ) :
    (Q p data).coeff k = if k < p + 2 then reflect (p * (p + 1 - k)) (data.Φ.coeff k) else 0 := by
  rw [Q, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

variable (p : ℕ) [hp : Fact p.Prime] (data : ModularPolynomialData p)

theorem natDegree_coeff_le (k : ℕ) : (data.Φ.coeff k).natDegree ≤ p * (p + 1 - k) := by
  have h := ModularCurve.ModularPolynomialData.natDegree_coeff_le_mul_dedekindPsi_sub_all p data k
  rwa [dedekindPsi_prime] at h

theorem coeff_natDegree_succ : data.Φ.coeff (p + 1) = 1 := by
  have h1 := data.monic
  have h2 : data.Φ.natDegree = p + 1 := data.natDegree_eq.trans (dedekindPsi_prime p)
  rw [Monic, leadingCoeff, h2] at h1
  exact h1

theorem coeff_eq_zero_of_lt (k : ℕ) (hk : p + 1 < k) : data.Φ.coeff k = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  rw [data.natDegree_eq, dedekindPsi_prime]; exact hk

theorem coeff_Q_succ : (Q p data).coeff (p + 1) = 1 := by
  rw [coeff_Q, if_pos (by omega), coeff_natDegree_succ, Nat.sub_self, mul_zero]
  rw [← C_1, reflect_C, pow_zero, mul_one]

theorem coeff_Q_eq_zero_of_lt (k : ℕ) (hk : p + 1 < k) : (Q p data).coeff k = 0 := by
  rw [coeff_Q]; split_ifs with h
  · rw [coeff_eq_zero_of_lt p data k hk, reflect_zero]
  · rfl

theorem natDegree_Q_le : (Q p data).natDegree ≤ p + 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  exact coeff_Q_eq_zero_of_lt p data k (by exact_mod_cast hk)

theorem natDegree_Q : (Q p data).natDegree = p + 1 :=
  le_antisymm (natDegree_Q_le p data) (le_natDegree_of_ne_zero (by rw [coeff_Q_succ]; exact one_ne_zero))

theorem monic_Q : (Q p data).Monic := by
  rw [Monic, leadingCoeff, natDegree_Q, coeff_Q_succ]

theorem eval_Q (S : Type*) [Field S] (x y : S) (hx : x ≠ 0)
    (h : data.Φ.eval₂ (eval₂RingHom (Int.castRingHom S) x) y = 0) :
    (Q p data).eval₂ (eval₂RingHom (Int.castRingHom S) x⁻¹) (y / x ^ p) = 0 := by
  letI : Invertible x := invertibleOfNonzero hx
  have hinv : (⅟ x : S) = x⁻¹ := invOf_eq_inv x

  have key : (Q p data).eval₂ (eval₂RingHom (Int.castRingHom S) x⁻¹) (y / x ^ p) * x ^ (p * (p + 1)) =
      data.Φ.eval₂ (eval₂RingHom (Int.castRingHom S) x) y := by
    conv_rhs => rw [eval₂_eq_sum_range' (eval₂RingHom (Int.castRingHom S) x)
      (show data.Φ.natDegree < p + 2 by rw [data.natDegree_eq, dedekindPsi_prime]; omega) y]
    rw [Q, eval₂_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [eval₂_mul, eval₂_C, eval₂_X_pow, coe_eval₂RingHom, coe_eval₂RingHom, ← hinv,
      div_eq_mul_inv, mul_pow, ← inv_pow, ← hinv]
    have hr := eval₂_reflect_mul_pow (Int.castRingHom S) x (p * (p + 1 - k)) (data.Φ.coeff k)
      (natDegree_coeff_le p data k)
    have hN : p * (p + 1 - k) + p * k = p * (p + 1) := by
      rw [← mul_add]; congr 1; omega
    rw [← hr]
    rw [show x ^ (p * (p + 1)) = x ^ (p * (p + 1 - k)) * x ^ (p * k) by rw [← pow_add, hN]]
    have hxk : (⅟ x ^ p) ^ k * x ^ (p * k) = 1 := by
      rw [← pow_mul, ← mul_pow, invOf_mul_self, one_pow]
    calc eval₂ (Int.castRingHom S) (⅟ x) (reflect (p * (p + 1 - k)) (data.Φ.coeff k)) * (y ^ k * (⅟ x ^ p) ^ k) *
          (x ^ (p * (p + 1 - k)) * x ^ (p * k))
        = eval₂ (Int.castRingHom S) (⅟ x) (reflect (p * (p + 1 - k)) (data.Φ.coeff k)) * x ^ (p * (p + 1 - k)) * y ^ k *
          ((⅟ x ^ p) ^ k * x ^ (p * k)) := by ring
      _ = eval₂ (Int.castRingHom S) (⅟ x) (reflect (p * (p + 1 - k)) (data.Φ.coeff k)) * x ^ (p * (p + 1 - k)) * y ^ k := by
          rw [hxk, mul_one]
  rw [h] at key
  exact (mul_eq_zero.mp key).resolve_right (pow_ne_zero _ hx)

theorem kronecker_expand :
    ((C X ^ p - X) * (C X - X ^ p) : Polynomial (Polynomial (ZMod p))) =
      C (X ^ (p + 1)) * X ^ 0 - C (X ^ p) * X ^ p - C X * X ^ 1 + C 1 * X ^ (p + 1) := by
  simp only [map_pow, map_one]; ring

theorem coeff_coeff_mod (k : ℕ) :
    (((data.Φ.coeff k).coeff (p * (p + 1 - k)) : ℤ) : ZMod p) =
      if k = p + 1 then 1 else if k = p then -1 else 0 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hKr := ModularCurve.kroneckerCongruence_of_prime p data
  rw [KroneckerCongruence, kronecker_expand] at hKr
  have h := congrArg (fun P : Polynomial (Polynomial (ZMod p)) => (P.coeff k).coeff (p * (p + 1 - k))) hKr
  simp only [reduceModBivar, coe_mapRingHom, coeff_map, eq_intCast] at h
  rw [h]
  simp only [coeff_add, coeff_sub, coeff_C_mul_X_pow]
  by_cases h1 : k = p + 1
  · subst h1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl, if_pos rfl, Nat.sub_self,
      mul_zero]
    simp
  by_cases h2 : k = p
  · subst h2
    rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg h1, if_pos rfl,
      show k * (k + 1 - k) = k by rw [Nat.add_sub_cancel_left, mul_one]]
    simp
  rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1, coeff_zero, sub_zero, add_zero]
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos rfl, if_neg (by omega), coeff_zero, sub_zero, Nat.sub_zero, coeff_X_pow, if_neg]
    intro hh
    have h3 : p * (p + 1) = 1 * (p + 1) := by omega
    have := Nat.eq_of_mul_eq_mul_right (by omega) h3
    omega
  by_cases h1' : k = 1
  · subst h1'
    rw [if_neg one_ne_zero, if_pos rfl, coeff_zero, zero_sub, coeff_X_of_ne_one, neg_zero]
    intro hh
    rw [Nat.add_sub_cancel] at hh
    have h4 : 2 * 2 ≤ p * p := Nat.mul_le_mul hp2 hp2
    omega
  rw [if_neg h0, if_neg h1', coeff_zero, sub_zero]

theorem map_Q (R : Type*) [CommRing R] [CharP R p] :
    (Q p data).map (eval₂RingHom (Int.castRingHom R) 0) = X ^ p * (X - 1) := by
  have hp1 : p + 1 ≠ p := by omega
  have hφ : ∀ m : ℤ, (Int.castRingHom R) m = ZMod.castHom (dvd_refl p) R (m : ZMod p) := fun m =>
    DFunLike.congr_fun (RingHom.ext_int (Int.castRingHom R) ((ZMod.castHom (dvd_refl p) R).comp (Int.castRingHom (ZMod p)))) m
  rw [show (X : Polynomial R) ^ p * (X - 1) = X ^ (p + 1) - X ^ p by ring]
  ext n
  rw [coeff_map, coeff_sub, coeff_X_pow, coeff_X_pow, coeff_Q]
  by_cases hn : n < p + 2
  · rw [if_pos hn, coe_eval₂RingHom, eval₂_at_zero, coeff_reflect, revAt_zero, hφ, coeff_coeff_mod p data n]
    by_cases h1 : n = p + 1
    · rw [if_pos h1, if_pos h1, if_neg (h1 ▸ hp1), map_one, sub_zero]
    · by_cases h2 : n = p
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2, map_neg, map_one, zero_sub]
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2, map_zero, sub_zero]
  · have h1 : n ≠ p + 1 := by omega
    have h2 : n ≠ p := by omega
    rw [if_neg hn, map_zero, if_neg h1, if_neg h2, sub_zero]

end CuspValAlphaK1

open CuspValAlphaK1 in
theorem solution
    (p : ℕ) [Fact p.Prime] (data : ModularPolynomialData p) :
    ∃ Q : Polynomial (Polynomial ℤ), Q.Monic ∧ Q.natDegree = p + 1 ∧
      (∀ (S : Type*) [Field S] (x y : S), x ≠ 0 →
          data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y = 0 →
          Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) (y / x ^ p) = 0) ∧
      (∀ (R : Type*) [CommRing R] [CharP R p],
          Q.map (Polynomial.eval₂RingHom (Int.castRingHom R) 0) = Polynomial.X ^ p * (Polynomial.X - 1)) :=
  ⟨Q p data, monic_Q p data, natDegree_Q p data, fun S _ x y hx h => eval_Q p data S x y hx h, fun R _ _ => map_Q p data R⟩

end S_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one (solution)
