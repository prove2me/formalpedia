-- Prove2me | solution 1 for LaurentSeries.eq_C_coeff_zero_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d8ea1f31-f1a6-59cd-ac26-c1e09ab443f9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic

set_option autoImplicit false

namespace LaurentSeries
namespace AlgClosedPort
p2m_open "LaurentSeries"

open HahnSeries Polynomial

variable {K : Type*} [Field K]

theorem algebraMap_eq_C (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem order_nonneg_of_isAlgebraic {x : LaurentSeries K} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    0 ≤ x.order := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hp0, hpx⟩ := hx
  set d := p.natDegree with hd
  have hne : (x ^ d).coeff (d • x.order) ≠ 0 := by
    rw [← HahnSeries.order_pow x d]
    exact (HahnSeries.coeff_order_eq_zero.not.mpr (pow_ne_zero d hx0))
  have key : (Polynomial.aeval x p).coeff (d • x.order)
      = p.coeff d * (x ^ d).coeff (d • x.order) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
    simp only [HahnSeries.coeff_sum, algebraMap_eq_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
      smul_eq_mul]
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hpi : p.coeff i = 0
    · rw [hpi, zero_mul]
    · have hlt : d • x.order < (x ^ i).order := by
        rw [HahnSeries.order_pow, nsmul_eq_mul, nsmul_eq_mul]
        have hi' : (i : ℤ) < (d : ℤ) := by exact_mod_cast hi
        nlinarith
      rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]
  have hlead : p.coeff d ≠ 0 := by
    rw [hd]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  have h : (Polynomial.aeval x p).coeff (d • x.order) ≠ 0 := by
    rw [key]; exact mul_ne_zero hlead hne
  apply h
  rw [hpx]
  rfl

theorem order_eq_zero_of_isAlgebraic {x : LaurentSeries K} (hx : IsAlgebraic K x) (hx0 : x ≠ 0) :
    x.order = 0 := by
  have h1 := order_nonneg_of_isAlgebraic hx hx0
  have h2 := order_nonneg_of_isAlgebraic hx.inv (inv_ne_zero hx0)
  have h3 : x.order + x⁻¹.order = 0 := by
    rw [← HahnSeries.order_mul hx0 (inv_ne_zero hx0), mul_inv_cancel₀ hx0, HahnSeries.order_one]
  omega

end LaurentSeries.AlgClosedPort

open LaurentSeries.AlgClosedPort in
theorem solution {K : Type*} [Field K] {x : LaurentSeries K} (hx : IsAlgebraic K x) :
    x = HahnSeries.C (x.coeff 0) := by
  set y : LaurentSeries K := x - HahnSeries.C (x.coeff 0) with hy
  have hyalg : IsAlgebraic K y := by
    refine hx.sub ?_
    rw [← algebraMap_eq_C]
    exact isAlgebraic_algebraMap _
  by_cases hy0 : y = 0
  · exact sub_eq_zero.mp hy0
  · exfalso
    have hord := order_eq_zero_of_isAlgebraic hyalg hy0
    have hc : y.coeff y.order ≠ 0 := HahnSeries.coeff_order_eq_zero.not.mpr hy0
    rw [hord] at hc
    apply hc
    simp [hy]

end S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
end P2MW
export P2MW.S_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic (solution)
