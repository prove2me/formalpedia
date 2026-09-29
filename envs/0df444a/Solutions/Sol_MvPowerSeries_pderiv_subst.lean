-- Prove2me | solution 1 for MvPowerSeries.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/bf64d256-4e50-5273-9a2b-95a8a594b97b

import Mathlib
import Theorems.Thm_MvPowerSeries_pderiv_mul
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_pderiv_subst

set_option autoImplicit false

open FormalGroup

namespace DW2P2

open MvPowerSeries

variable {σ : Type*} {R : Type*} [CommRing R]

theorem pderiv_one' (i : σ) : MvPowerSeries.pderivLin i (1 : MvPowerSeries σ R) = 0 := by
  classical
  ext d
  rw [MvPowerSeries.kw_coeff_pderiv, MvPowerSeries.coeff_one, if_neg, smul_zero, MvPowerSeries.coeff_zero]
  intro h
  have := congrArg (fun e => e i) h
  simp at this

theorem pderiv_pow_succ (i : σ) (a : MvPowerSeries σ R) (n : ℕ) :
    MvPowerSeries.pderivLin i (a ^ (n + 1)) = ((n + 1 : ℕ) : MvPowerSeries σ R) * a ^ n * MvPowerSeries.pderivLin i a := by
  induction n with
  | zero => rw [_root_.zero_add, pow_one, pow_zero]; push_cast; ring
  | succ n ih =>
    rw [pow_succ, MvPowerSeries.pderiv_mul, ih]
    push_cast; ring

theorem coeff_pow_eq_zero (a : MvPowerSeries σ R) (ha : MvPowerSeries.constantCoeff a = 0) {e : σ →₀ ℕ} {n : ℕ}
    (h : e.degree < n) : MvPowerSeries.coeff e (a ^ n) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n ha)

theorem coeff_pow_mul_eq_zero (a b : MvPowerSeries σ R) (ha : MvPowerSeries.constantCoeff a = 0) {e : σ →₀ ℕ} {n : ℕ}
    (h : e.degree < n) : MvPowerSeries.coeff e (a ^ n * b) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_ MvPowerSeries.le_order_mul
  exact lt_of_lt_of_le (lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n ha))
    le_self_add

theorem coeff_subst_eq_sum (a : MvPowerSeries σ R) (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R)
    (e : σ →₀ ℕ) (N : ℕ) (hN : e.degree < N) :
    MvPowerSeries.coeff e (PowerSeries.subst a h) = ∑ n ∈ Finset.range N, PowerSeries.coeff n h • MvPowerSeries.coeff e (a ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  rw [Finset.coe_range, Set.mem_Iio]
  by_contra hlt
  apply hn
  simp only
  rw [coeff_pow_eq_zero a ha (lt_of_lt_of_le hN (not_lt.mp hlt)), smul_zero]

end DW2P2

theorem solution
    {σ : Type*} {R : Type*} [CommRing R] (i : σ) (a : MvPowerSeries σ R)
    (ha : MvPowerSeries.constantCoeff a = 0) (h : PowerSeries R) :
    MvPowerSeries.pderivLin i (PowerSeries.subst a h) =
      PowerSeries.subst a (PowerSeries.derivative R h) * MvPowerSeries.pderivLin i a := by
  classical
  ext d
  set K := d.degree + 1 with hK
  have hdeg1 : (d + Finsupp.single i 1).degree = d.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hne : d + Finsupp.single i 1 ≠ 0 := by
    intro h0
    have := congrArg (fun e => e i) h0
    simp at this

  have hL : MvPowerSeries.coeff d (MvPowerSeries.pderivLin i (PowerSeries.subst a h))
      = ∑ m ∈ Finset.range K, (PowerSeries.coeff (m + 1) h * (m + 1)) • MvPowerSeries.coeff d (a ^ m * MvPowerSeries.pderivLin i a) := by
    rw [MvPowerSeries.kw_coeff_pderiv,
      DW2P2.coeff_subst_eq_sum a ha h (d + Finsupp.single i 1) (K + 1) (by rw [hdeg1, hK]; omega),
      Finset.smul_sum, Finset.sum_range_succ', pow_zero, MvPowerSeries.coeff_one, if_neg hne, smul_zero, smul_zero, _root_.add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_comm, ← MvPowerSeries.kw_coeff_pderiv, DW2P2.pderiv_pow_succ, mul_assoc,
      ← map_natCast (MvPowerSeries.C (σ := σ) (R := R)), MvPowerSeries.coeff_C_mul, smul_eq_mul, smul_eq_mul]
    push_cast; ring

  have hin : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal d, MvPowerSeries.coeff x.1 (PowerSeries.subst a (PowerSeries.derivative R h))
      * MvPowerSeries.coeff x.2 (MvPowerSeries.pderivLin i a)
      = ∑ m ∈ Finset.range (K + 1), PowerSeries.coeff m (PowerSeries.derivative R h)
          • (MvPowerSeries.coeff x.1 (a ^ m) * MvPowerSeries.coeff x.2 (MvPowerSeries.pderivLin i a)) := by
    intro x hx
    have hxd : (x.1 : σ →₀ ℕ).degree ≤ d.degree := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      rw [← hx, map_add]; omega
    rw [DW2P2.coeff_subst_eq_sum a ha _ x.1 (K + 1) (by rw [hK]; omega), Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_mul_assoc]
  have hR : MvPowerSeries.coeff d (PowerSeries.subst a (PowerSeries.derivative R h) * MvPowerSeries.pderivLin i a)
      = ∑ m ∈ Finset.range K, (PowerSeries.coeff (m + 1) h * (m + 1)) • MvPowerSeries.coeff d (a ^ m * MvPowerSeries.pderivLin i a) := by
    rw [MvPowerSeries.coeff_mul, Finset.sum_congr rfl hin, Finset.sum_comm]
    simp only [← Finset.smul_sum, ← MvPowerSeries.coeff_mul]
    rw [Finset.sum_range_succ, DW2P2.coeff_pow_mul_eq_zero a _ ha (show d.degree < K by rw [hK]; omega), smul_zero, _root_.add_zero]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [PowerSeries.coeff_derivative]
  rw [hL, hR]

end S_MvPowerSeries_pderiv_subst
end P2MW
export P2MW.S_MvPowerSeries_pderiv_subst (solution)
