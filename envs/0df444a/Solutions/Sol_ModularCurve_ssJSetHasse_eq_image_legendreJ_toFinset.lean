-- Prove2me | solution 1 for ModularCurve.ssJSetHasse_eq_image_legendreJ_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3d91ae99-1d06-5345-915d-3a77ea8a4bd7

import Mathlib
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_Polynomial_DeuringPolynomial
import Definitions.Def_ModularCurve_LegendreJ
import Theorems.Thm_ModularCurve_ssJSetHasse_eq_image_legendreJ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset

set_option autoImplicit false

p2m_open "Polynomial P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset.Polynomial"

noncomputable section

namespace Polynomial
p2m_export "Polynomial" "C mem_roots' C_comp X mul_comp coeff monomial eval_finsetSum degree C_pow map eval_zero comp roots pow_comp X_comp natDegree as_sum_range' C_mul_X_pow_eq_monomial coeff_X_pow_mul coeff_X_add_C_pow C_neg coeff_C_mul finsetSum_coeff sum_comp coeff_eq_zero_of_natDegree_lt mod ext ring coeff_mul eval deuringPolynomial"
p2m_open "Polynomial"

theorem coeff_X_sub_one_mul_X_sub_C_pow_self {R : Type*} [CommRing R] (t : R) (m : ℕ) :
    (((X - C 1) * (X - C t)) ^ m).coeff m
      = (-1) ^ m * ∑ i ∈ Finset.range (m + 1), ((m.choose i : R) ^ 2) * t ^ i := by
  rw [mul_pow, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
  rw [Nat.choose_symm hi', Nat.sub_sub_self hi']
  have : (-1 : R) ^ m = (-1) ^ (m - i) * (-1) ^ i := by rw [← pow_add, Nat.sub_add_cancel hi']
  rw [this, neg_pow t]
  ring

theorem coeff_C_mul_X_pow_mul' {R : Type*} [CommRing R] (c : R) (p : R[X]) (m d : ℕ) :
    (C c * X ^ m * p).coeff (d + m) = c * p.coeff d := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul]

theorem eval_map_deuringPolynomial {R : Type*} [CommRing R] (q : ℕ) (t : R) :
    ((deuringPolynomial q).map (Int.castRingHom R)).eval t
      = ∑ i ∈ Finset.range ((q - 1) / 2 + 1), ((((q - 1) / 2).choose i : R)) ^ 2 * t ^ i := by
  simp [deuringPolynomial, Polynomial.map_sum, eval_finsetSum]

theorem natCast_choose_prime_sub_one_eq_zero {R : Type*} [CommRing R] {q : ℕ} [hp : Fact q.Prime]
    [CharP R q] {k : ℕ} (h1 : q - 1 < k) (h2 : k ≤ 2 * q - 2) :
    ((k.choose (q - 1) : ℕ) : R) = 0 := by
  rw [CharP.cast_eq_zero_iff R q]
  have hq := hp.out.one_lt
  exact hp.out.dvd_choose (by omega) (by omega) (by omega)

theorem coeff_comp_C_mul_X_sub_C_of_charP {R : Type*} [CommRing R] {q : ℕ} [hp : Fact q.Prime]
    [CharP R q] (P : R[X]) (hP : P.natDegree ≤ 2 * q - 2) (a r : R) :
    (P.comp (C a * (X - C r))).coeff (q - 1) = a ^ (q - 1) * P.coeff (q - 1) := by
  have hq := hp.out.one_lt
  conv_lhs => rw [P.as_sum_range' (2 * q - 1) (by omega), sum_comp, finsetSum_coeff]
  have hterm : ∀ i, ((monomial i (P.coeff i)).comp (C a * (X - C r))).coeff (q - 1)
      = P.coeff i * (a ^ i * ((-r) ^ (i - (q - 1)) * (i.choose (q - 1) : R))) := by
    intro i
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, pow_comp, X_comp, mul_pow, ← C_pow, coeff_C_mul,
      coeff_C_mul, sub_eq_add_neg, ← C_neg, coeff_X_add_C_pow]
  simp_rw [hterm]
  rw [Finset.sum_eq_single (q - 1)]
  · simp
    ring
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · rw [Nat.choose_eq_zero_of_lt hlt]; simp
    · by_cases hi2 : i ≤ 2 * q - 2
      · rw [natCast_choose_prime_sub_one_eq_zero (R := R) hgt hi2]; simp
      · have : P.coeff i = 0 := P.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [this]; simp
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

theorem eval_zero_map_deuringPolynomial' {R : Type*} [CommRing R] (q : ℕ) :
    ((deuringPolynomial q).map (Int.castRingHom R)).eval 0 = 1 := by
  rw [eval_map_deuringPolynomial, Finset.sum_range_succ']
  simp

theorem map_deuringPolynomial_ne_zero' {R : Type*} [CommRing R] [Nontrivial R] (q : ℕ) :
    (deuringPolynomial q).map (Int.castRingHom R) ≠ 0 := fun h => by
  have := eval_zero_map_deuringPolynomial' (R := R) q
  rw [h, eval_zero] at this
  exact zero_ne_one this

theorem eval_one_map_deuringPolynomial_ne_zero' {K : Type*} [Field K] (q : ℕ) [hp : Fact q.Prime]
    [CharP K q] : ((deuringPolynomial q).map (Int.castRingHom K)).eval 1 ≠ 0 := by
  rw [eval_map_deuringPolynomial]
  simp only [one_pow, mul_one, ← Nat.cast_pow, ← Nat.cast_sum, Nat.sum_range_choose_sq, Ne,
    CharP.cast_eq_zero_iff K q]
  intro h
  have hq := hp.out.two_le
  set m := (q - 1) / 2 with hm
  have hdvd : (2 * m).choose m ∣ (2 * m).factorial :=
    ⟨m.factorial * (2 * m - m).factorial, by
      rw [← mul_assoc]; exact (Nat.choose_mul_factorial_mul_factorial (by omega)).symm⟩
  have := (hp.out.dvd_factorial).mp (h.trans hdvd)
  omega

end Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "ssJSetHasse legendreJ ssJSetHasse_eq_image_legendreJ"
p2m_open "ModularCurve"

open WeierstrassCurve

theorem ssJSetHasse_eq_image_legendreJ_toFinset' (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (K : Type*)
    [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSetHasse q K
      = legendreJ '' ↑(((Polynomial.deuringPolynomial q).map (Int.castRingHom K)).roots.toFinset) := by
  rw [ssJSetHasse_eq_image_legendreJ q hq K]
  congr 1
  ext t
  simp [Polynomial.mem_roots', map_deuringPolynomial_ne_zero']

end ModularCurve

end

p2m_open "Polynomial P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset.Polynomial ModularCurve P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset.ModularCurve"

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (K : Type*)
    [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSetHasse q K
      = legendreJ '' ↑(((Polynomial.deuringPolynomial q).map (Int.castRingHom K)).roots.toFinset) :=
  ModularCurve.ssJSetHasse_eq_image_legendreJ_toFinset' q hq K

end S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset
end P2MW
export P2MW.S_ModularCurve_ssJSetHasse_eq_image_legendreJ_toFinset (solution)
