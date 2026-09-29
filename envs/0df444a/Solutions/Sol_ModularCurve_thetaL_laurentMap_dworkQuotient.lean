-- Prove2me | solution 1 for ModularCurve.thetaL_laurentMap_dworkQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/a6382e91-ea54-5839-9fbf-28292579ffff

import Mathlib
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_thetaL_laurentMap_dworkQuotient

set_option autoImplicit false

p2m_open "HahnSeries ModularCurve P2MW.S_ModularCurve_thetaL_laurentMap_dworkQuotient.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "laurentMap laurentMap_coeff laurentMap_qExpand laurentMap_laurentMap jqInt qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd thetaL thetaL_apply pow_char_eq_map_frobenius_qExpand"
namespace K2b
p2m_open "ModularCurve"

section ThetaR

variable {R : Type*} [CommRing R]

noncomputable def thetaR (f : LaurentSeries R) : LaurentSeries R :=
  single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f

theorem coeff_single_one_mul_derivative_add_one (f : LaurentSeries R) (m : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff (m + 1) =
      ((m + 1 : ℤ) : R) * f.coeff (m + 1) := by
  rw [HahnSeries.coeff_single_mul_add, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right, zsmul_eq_mul]
  simp only [Nat.cast_one]

theorem coeff_single_one_mul_derivative (f : LaurentSeries R) (n : ℤ) :
    (single (1 : ℤ) (1 : R) * LaurentSeries.derivative R f).coeff n = (n : R) * f.coeff n := by
  have h := coeff_single_one_mul_derivative_add_one f (n - 1)
  simp only [sub_add_cancel] at h
  exact h

theorem coeff_thetaR (f : LaurentSeries R) (n : ℤ) : (thetaR f).coeff n = (n : R) * f.coeff n :=
  coeff_single_one_mul_derivative f n

theorem thetaR_add (f g : LaurentSeries R) : thetaR (f + g) = thetaR f + thetaR g := by
  ext n; simp [coeff_thetaR, mul_add]

theorem thetaR_sub (f g : LaurentSeries R) : thetaR (f - g) = thetaR f - thetaR g := by
  ext n; simp [coeff_thetaR, mul_sub]

theorem thetaR_natCast_mul (m : ℕ) (f : LaurentSeries R) :
    thetaR ((m : LaurentSeries R) * f) = (m : LaurentSeries R) * thetaR f := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) m, HahnSeries.C_mul_eq_smul,
    HahnSeries.C_mul_eq_smul, coeff_thetaR, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
    coeff_thetaR, smul_eq_mul, smul_eq_mul]
  ring

theorem support_thetaR_subset (f : LaurentSeries R) : (thetaR f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, coeff_thetaR] at hn
  rw [HahnSeries.mem_support]
  exact right_ne_zero_of_mul hn

theorem thetaR_mul (f g : LaurentSeries R) : thetaR (f * g) = thetaR f * g + f * thetaR g := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaR, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (support_thetaR_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_thetaR_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  rw [coeff_thetaR, coeff_thetaR, ← hsum, Int.cast_add]
  ring

theorem thetaR_pow (f : LaurentSeries R) (m : ℕ) :
    thetaR (f ^ (m + 1)) = ((m + 1 : ℕ) : LaurentSeries R) * (f ^ m * thetaR f) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, thetaR_mul, ih]
    push_cast
    ring

theorem thetaR_qExpand (N : ℕ) [NeZero N] (f : LaurentSeries R) :
    thetaR (qExpand R N f) = (N : LaurentSeries R) * qExpand R N (thetaR f) := by
  ext n
  rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := R)) N, HahnSeries.C_mul_eq_smul,
    HahnSeries.coeff_smul, smul_eq_mul, coeff_thetaR]
  by_cases hn : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hn
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeff_thetaR, Int.cast_mul, Int.cast_natCast]
    ring
  · rw [qExpand_coeff_of_not_dvd N _ hn, qExpand_coeff_of_not_dvd N _ hn, mul_zero, mul_zero]

theorem laurentMap_thetaR {k : Type*} [Field k] (φ : R →+* k) (f : LaurentSeries R) :
    laurentMap φ (thetaR f) = thetaL k (laurentMap φ f) := by
  ext n
  rw [thetaL_apply, coeff_single_one_mul_derivative, laurentMap_coeff, coeff_thetaR, map_mul,
    map_intCast, laurentMap_coeff]

end ThetaR

theorem laurentMap_pow_eq_qExpand (q : ℕ) [Fact q.Prime] {k : Type*} [Field k] [CharP k q]
    (t : LaurentSeries ℤ) :
    laurentMap (Int.castRingHom k) t ^ q = qExpand k q (laurentMap (Int.castRingHom k) t) := by
  rw [pow_char_eq_map_frobenius_qExpand q]
  change laurentMap (frobenius k q) (qExpand k q (laurentMap (Int.castRingHom k) t)) = _
  rw [laurentMap_qExpand, laurentMap_laurentMap]
  have hcomp : (frobenius k q).comp (Int.castRingHom k) = Int.castRingHom k := RingHom.ext_int _ _
  rw [hcomp]

theorem main (q : ℕ) [Fact q.Prime]
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q jqInt - jqInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    thetaL k (laurentMap (Int.castRingHom k) S) =
      thetaL k (laurentMap (Int.castRingHom k) jqInt) ^ q
        - laurentMap (Int.castRingHom k) jqInt ^ (q - 1) * thetaL k (laurentMap (Int.castRingHom k) jqInt) := by
  have hqprime : q.Prime := Fact.out
  obtain ⟨m, hm⟩ : ∃ m : ℕ, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hqprime.pos).symm⟩
  set J : LaurentSeries ℤ := jqInt with hJ
  set φ := Int.castRingHom k with hφ
  have hqL0 : ((q : LaurentSeries ℤ)) ≠ 0 := by
    rw [← map_natCast (HahnSeries.C (Γ := ℤ) (R := ℤ)) q]
    intro h
    exact (Int.natCast_ne_zero.mpr hqprime.ne_zero) (HahnSeries.C_injective (h.trans HahnSeries.C_zero.symm))

  have h1 := congrArg thetaR hS
  rw [thetaR_sub, thetaR_qExpand, thetaR_natCast_mul] at h1
  have h2 : thetaR (J ^ q) = (q : LaurentSeries ℤ) * (J ^ (q - 1) * thetaR J) := by
    rw [hm, Nat.add_sub_cancel, thetaR_pow]
  rw [h2, ← mul_sub] at h1
  have h3 : qExpand ℤ q (thetaR J) - J ^ (q - 1) * thetaR J = thetaR S := mul_left_cancel₀ hqL0 h1

  have h4 := congrArg (laurentMap φ) h3
  rw [map_sub, map_mul, map_pow, laurentMap_qExpand, laurentMap_thetaR] at h4

  have h5 : qExpand k q (thetaL k (laurentMap φ J)) = thetaL k (laurentMap φ J) ^ q := by
    rw [← laurentMap_thetaR, hφ, laurentMap_pow_eq_qExpand q]
  rw [h5, laurentMap_thetaR] at h4
  exact h4.symm

end ModularCurve.K2b

theorem solution (q : ℕ) [Fact q.Prime]
    (S : LaurentSeries ℤ) (hS : qExpand ℤ q jqInt - jqInt ^ q = (q : LaurentSeries ℤ) * S)
    (k : Type*) [Field k] [CharP k q] :
    thetaL k (laurentMap (Int.castRingHom k) S) =
      thetaL k (laurentMap (Int.castRingHom k) jqInt) ^ q
        - laurentMap (Int.castRingHom k) jqInt ^ (q - 1) * thetaL k (laurentMap (Int.castRingHom k) jqInt) :=
  ModularCurve.K2b.main q S hS k

end S_ModularCurve_thetaL_laurentMap_dworkQuotient
end P2MW
export P2MW.S_ModularCurve_thetaL_laurentMap_dworkQuotient (solution)
