-- Prove2me | solution 1 for ModularCurve.CharPModel.exists_monic_eval2_inv_mul_inv_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/4bbb7ce1-168a-5b04-b668-b640755151ef

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero

open Polynomial
open scoped Polynomial.Bivariate

namespace CharpS10bB

theorem eval₂_reflect_inv {R K : Type*} [CommRing R] [Field K] (f : R →+* K) {x : K} (hx : x ≠ 0)
    (D : ℕ) (a : R[X]) (ha : a.natDegree ≤ D) :
    eval₂ f x⁻¹ (reflect D a) = eval₂ f x a * x⁻¹ ^ D := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := eval₂_reflect_mul_pow f x⁻¹ D a ha
  rw [invOf_eq_inv, inv_inv] at h

  letI : Invertible x := invertibleOfNonzero hx
  have h' := eval₂_reflect_mul_pow f x D a ha
  rw [invOf_eq_inv] at h'

  calc eval₂ f x⁻¹ (reflect D a)
      = eval₂ f x⁻¹ (reflect D a) * x ^ D * x⁻¹ ^ D := by
        rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, mul_one]
    _ = eval₂ f x a * x⁻¹ ^ D := by rw [h']

theorem exists_monic_eval₂_inv_mul_inv_pow_eq_zero {R K : Type*} [CommRing R] [Nontrivial R]
    [Field K] (f : R →+* K) (P : R[X][Y]) (hP : P.Monic) (m : ℕ)
    (hdeg : ∀ i < P.natDegree, (P.coeff i).natDegree ≤ m * (P.natDegree - i))
    {x : K} (hx : x ≠ 0) (y : K) (hroot : P.eval₂ (eval₂RingHom f x) y = 0) :
    ∃ Q : R[X][Y], Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.eval₂ (eval₂RingHom f x⁻¹) (y * x⁻¹ ^ m) = 0 := by
  set n := P.natDegree with hn

  let c : ℕ → R[X] := fun i ↦ reflect (m * (n - i)) (P.coeff i)
  let Q : R[X][Y] := Y ^ n + ∑ i : Fin n, C (c i) * Y ^ (i : ℕ)
  have hQmonic : Q.Monic := by
    refine (monic_X_pow n).add_of_left ?_
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have hQdeg : Q.natDegree = n := by
    have h1 : (Y ^ n + ∑ i : Fin n, C (c i) * Y ^ (i : ℕ) : R[X][Y]).natDegree
        = (Y ^ n : R[X][Y]).natDegree :=
      natDegree_add_eq_left_of_degree_lt (by rw [degree_X_pow]; exact degree_sum_fin_lt _)
    rw [h1, natDegree_X_pow]
  refine ⟨Q, hQmonic, hQdeg, ?_⟩

  set φ : R[X] →+* K := eval₂RingHom f x with hφ
  set φ' : R[X] →+* K := eval₂RingHom f x⁻¹ with hφ'
  set z : K := y * x⁻¹ ^ m with hz
  have hcn : c n = 1 := by
    simp only [c, Nat.sub_self, mul_zero]
    rw [show P.coeff n = 1 from hP.coeff_natDegree, ← C_1, reflect_C, pow_zero, mul_one]
  have hterm : ∀ i ≤ n, φ' (c i) * z ^ i = x⁻¹ ^ (m * n) * (φ (P.coeff i) * y ^ i) := by
    intro i hi
    have hdi : (P.coeff i).natDegree ≤ m * (n - i) := by
      rcases lt_or_eq_of_le hi with hlt | rfl
      · exact hdeg i hlt
      · rw [show P.coeff n = 1 from hP.coeff_natDegree, natDegree_one]
        exact Nat.zero_le _
    have h1 : φ' (c i) = φ (P.coeff i) * x⁻¹ ^ (m * (n - i)) := by
      simp only [hφ', hφ, coe_eval₂RingHom, c]
      exact eval₂_reflect_inv f hx _ _ hdi
    rw [h1, hz, mul_pow, ← pow_mul]
    have hexp : m * (n - i) + m * i = m * n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hi]
    calc φ (P.coeff i) * x⁻¹ ^ (m * (n - i)) * (y ^ i * x⁻¹ ^ (m * i))
        = φ (P.coeff i) * y ^ i * (x⁻¹ ^ (m * (n - i)) * x⁻¹ ^ (m * i)) := by ring
      _ = φ (P.coeff i) * y ^ i * x⁻¹ ^ (m * n) := by rw [← pow_add, hexp]
      _ = x⁻¹ ^ (m * n) * (φ (P.coeff i) * y ^ i) := by ring

  have hevalQ : Q.eval₂ φ' z = ∑ i ∈ Finset.range (n + 1), φ' (c i) * z ^ i := by
    simp only [Q, eval₂_add, eval₂_X_pow, eval₂_finsetSum, eval₂_mul, eval₂_C]
    rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range (fun i ↦ φ' (c i) * z ^ i) n, hcn,
      map_one, one_mul, add_comm]
  have hevalP : P.eval₂ φ y = ∑ i ∈ Finset.range (n + 1), φ (P.coeff i) * y ^ i :=
    eval₂_eq_sum_range φ y
  rw [hevalQ]
  calc ∑ i ∈ Finset.range (n + 1), φ' (c i) * z ^ i
      = ∑ i ∈ Finset.range (n + 1), x⁻¹ ^ (m * n) * (φ (P.coeff i) * y ^ i) := by
        refine Finset.sum_congr rfl fun i hi ↦ hterm i ?_
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    _ = x⁻¹ ^ (m * n) * P.eval₂ φ y := by rw [hevalP, Finset.mul_sum]
    _ = 0 := by rw [hroot, mul_zero]

end CharpS10bB

theorem solution {R K : Type*} [CommRing R] [Nontrivial R]
    [Field K] (f : R →+* K) (P : R[X][Y]) (hP : P.Monic) (m : ℕ)
    (hdeg : ∀ i < P.natDegree, (P.coeff i).natDegree ≤ m * (P.natDegree - i))
    {x : K} (hx : x ≠ 0) (y : K) (hroot : P.eval₂ (eval₂RingHom f x) y = 0) :
    ∃ Q : R[X][Y], Q.Monic ∧ Q.natDegree = P.natDegree ∧
      Q.eval₂ (eval₂RingHom f x⁻¹) (y * x⁻¹ ^ m) = 0 :=
  CharpS10bB.exists_monic_eval₂_inv_mul_inv_pow_eq_zero f P hP m hdeg hx y hroot

end S_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero
end P2MW
export P2MW.S_ModularCurve_CharPModel_exists_monic_eval2_inv_mul_inv_pow_eq_zero (solution)
