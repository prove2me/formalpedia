-- Prove2me | solution 1 for LaurentSeries.exists_eq_C_of_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ca343384-6913-5233-8d09-e067cd43962e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_exists_eq_C_of_isAlgebraic

universe u

set_option autoImplicit false

namespace LaurentSeries
p2m_export "LaurentSeries" "algebraMap_apply"
p2m_open "LaurentSeries"

open HahnSeries Polynomial

variable {K : Type u} [Field K]

theorem algebraMap_eq_C (c : K) : algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C]

theorem coeff_C_mul' (c : K) (y : LaurentSeries K) (a : ℤ) : (HahnSeries.C c * y).coeff a = c * y.coeff a :=
  HahnSeries.coeff_single_zero_mul

theorem order_eq_zero_of_isAlgebraic (x : LaurentSeries K) (hx : IsAlgebraic K x) (h0 : x ≠ 0) :
    x.order = 0 := by
  classical
  by_contra hn
  obtain ⟨p, hp0, hpx⟩ := hx
  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨i₀, hi₀, hmin⟩ := p.support.exists_min_image (fun i : ℕ => (i : ℤ) * x.order) hsupp
  have hstrict : ∀ i ∈ p.support, i ≠ i₀ → (i₀ : ℤ) * x.order < (i : ℤ) * x.order := by
    intro i hi hne
    refine lt_of_le_of_ne (hmin i hi) ?_
    intro heq
    apply hne
    have := mul_right_cancel₀ hn heq
    exact_mod_cast this.symm

  have hpx' : (∑ i ∈ p.support, HahnSeries.C (p.coeff i) * x ^ i) = 0 := by
    rw [← hpx, aeval_def, eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algebraMap_eq_C]
  have hrel := congrArg (fun y : LaurentSeries K => y.coeff ((i₀ : ℤ) * x.order)) hpx'
  simp only [HahnSeries.coeff_zero] at hrel
  rw [HahnSeries.coeff_sum, Finset.sum_eq_single i₀] at hrel
  · have hx0 : x ^ i₀ ≠ 0 := pow_ne_zero _ h0
    have hord : (x ^ i₀).order = (i₀ : ℤ) * x.order := by
      rw [HahnSeries.order_pow, nsmul_eq_mul]
    rw [coeff_C_mul', ← hord] at hrel
    exact (mul_ne_zero (Polynomial.mem_support_iff.mp hi₀) (mt HahnSeries.coeff_order_eq_zero.mp hx0)) hrel
  · intro i hi hne
    rw [coeff_C_mul', HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
    rw [HahnSeries.order_pow, nsmul_eq_mul]
    exact hstrict i hi hne
  · intro h
    exact absurd hi₀ h

theorem exists_eq_C_of_isAlgebraic (x : LaurentSeries K) (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by
  refine ⟨x.coeff 0, ?_⟩
  have hCa : ∀ c : K, (algebraMap K (LaurentSeries K) c) = HahnSeries.C c := algebraMap_eq_C
  set y : LaurentSeries K := x - algebraMap K (LaurentSeries K) (x.coeff 0) with hy
  have hyalg : IsAlgebraic K y :=
    hx.sub (isAlgebraic_algebraMap (R := K) (A := LaurentSeries K) (x.coeff 0))
  by_cases hy0 : y = 0
  · rw [hy, sub_eq_zero] at hy0
    rw [← hCa]
    exact hy0
  · exfalso
    have hord := order_eq_zero_of_isAlgebraic y hyalg hy0
    have hcoeff : y.coeff 0 = 0 := by
      rw [hy, HahnSeries.coeff_sub, hCa, HahnSeries.C_apply, HahnSeries.coeff_single_same, sub_self]
    have := mt HahnSeries.coeff_order_eq_zero.mp hy0
    rw [hord, hcoeff] at this
    exact this rfl

end LaurentSeries

theorem solution
    {K : Type u} [Field K] (x : LaurentSeries K) (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c :=
  LaurentSeries.exists_eq_C_of_isAlgebraic x hx

end S_LaurentSeries_exists_eq_C_of_isAlgebraic
end P2MW
export P2MW.S_LaurentSeries_exists_eq_C_of_isAlgebraic (solution)
