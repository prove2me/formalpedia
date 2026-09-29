-- Prove2me | solution 1 for ModularCurve.qExpand_linearIndependent_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4cd0cf32-0b66-5545-9941-eac4bad69efe

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_LaurentSeries_coeff_pow_char
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpand_linearIndependent_pow

set_option autoImplicit false

open Polynomial

open ModularCurve in

theorem solution (κ : Type*) [Field κ] (q : ℕ) [Fact q.Prime] [CharP κ q]
    (j : LaurentSeries κ) (hj : j.coeff (-1) ≠ 0) (e : Fin q → LaurentSeries κ)
    (h : ∑ m, ModularCurve.qExpand κ q (e m) * j ^ (m : ℕ) = 0) : ∀ m, e m = 0 := by
  classical
  have hq : q.Prime := Fact.out
  haveI : CharP (LaurentSeries κ) q :=
    charP_of_injective_algebraMap (algebraMap κ (LaurentSeries κ)).injective q
  let P : Subfield (LaurentSeries κ) := (qExpand κ q).fieldRange

  have hP : ∀ x ∈ P, ∀ n : ℤ, ¬ (q : ℤ) ∣ n → x.coeff n = 0 := by
    rintro x ⟨y, rfl⟩ n hn
    exact qExpand_coeff_of_not_dvd _ _ hn
  have hjP : j ∉ P := by
    intro hjm
    apply hj (hP j hjm (-1) ?_)
    intro hd
    have h1 := Int.le_of_dvd one_pos (Int.dvd_neg.mp hd)
    have h2 := hq.two_le
    omega

  have hjq : j ^ q ∈ P := by
    refine ⟨j.map (frobenius κ q), ?_⟩
    ext n
    rw [LaurentSeries.coeff_pow_char]
    by_cases hn : (q : ℤ) ∣ n
    · obtain ⟨m, rfl⟩ := hn
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
      rw [qExpand_coeff_mul, HahnSeries.map_coeff, if_pos ⟨m, rfl⟩, Int.mul_ediv_cancel_left _ hq0,
        frobenius_def]
    · rw [qExpand_coeff_of_not_dvd _ _ hn, if_neg hn]

  set a : P := ⟨j ^ q, hjq⟩ with ha
  have hirr : Irreducible (X ^ q - C a) := by
    refine X_pow_sub_C_irreducible_of_prime hq fun b hb => ?_
    apply hjP
    have hb' : ((b : LaurentSeries κ)) ^ q = j ^ q := by
      have := congrArg (fun z : P => (z : LaurentSeries κ)) hb
      simpa using this
    have hbj : (b : LaurentSeries κ) = j := by
      have h0 : ((b : LaurentSeries κ) - j) ^ q = 0 := by rw [sub_pow_char, hb', sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (hq.ne_zero) |>.mp h0)
    rw [← hbj]; exact b.2

  have hmin : minpoly P j = X ^ q - C a := by
    symm
    refine minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C a hq.ne_zero)
    rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    rfl
  have hdeg : (minpoly P j).natDegree = q := by
    rw [hmin, natDegree_X_pow_sub_C]

  have hli := linearIndependent_pow (K := P) j
  rw [hdeg] at hli
  have hli' := Fintype.linearIndependent_iff.mp hli
    (fun m => (⟨qExpand κ q (e m), ⟨e m, rfl⟩⟩ : P)) ?_
  · intro m
    have := congrArg (fun z : P => (z : LaurentSeries κ)) (hli' m)
    simp only [ZeroMemClass.coe_zero] at this
    exact (qExpand κ q).injective (by rw [this, map_zero])
  · rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Subfield.smul_def, smul_eq_mul]

end S_ModularCurve_qExpand_linearIndependent_pow
end P2MW
export P2MW.S_ModularCurve_qExpand_linearIndependent_pow (solution)
