-- Prove2me | solution 1 for N25.canonicalAChartLinearRemainder25_mod_z_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:59.461201+00:00
-- url     : https://prove2.me/submissions/017a52b9-28e8-442d-b0b4-71a5eae7ee56

import Mathlib
import Theorems.Thm_N25_canonicalAChartQuadratic25_monic
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_algebraMap_adjoinRoot_of_monic
import Theorems.Thm_N25_canonicalAChartBaseX25_not_mem_z
import Theorems.Thm_N25_canonicalAChartLinearRemainder25_mk
import Theorems.Thm_N25_canonicalAChartQuadratic25_root_equation

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance xSpecialization_semiring_s41eef0 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

local instance zSpecialization_semiring_s41eef0 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- Setting z=0 leaves the cubic regular in the monic quadric extension. -/
theorem _root_.solution :
    let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
      Ideal.Quotient.mk _
    IsRegular (AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π)) := by
  dsimp only
  let I := Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))
  let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸ I) := Ideal.Quotient.mk I
  have hp : Prime (canonicalAChartBaseZ25 K) := Polynomial.prime_C_iff.mpr (prime_X (R := K))
  have hIp : I.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  letI : IsDomain (CanonicalAChartBase25 K ⧸ I) := (Ideal.Quotient.isDomain_iff_prime I).mpr hIp
  let q := (canonicalAChartQuadratic25 K).map π
  let ι := AdjoinRoot.of q
  let y := AdjoinRoot.root q
  let x := ι (π (canonicalAChartBaseX25 K))
  have hz : π (canonicalAChartBaseZ25 K) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hx : π (canonicalAChartBaseX25 K) ≠ 0 := by
    intro h
    exact canonicalAChartBaseX25_not_mem_z K (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hxm : IsRegular x := isRegular_algebraMap_adjoinRoot_of_monic
    q ((canonicalAChartQuadratic25_monic K).map π) hx
  have hq : y^2-x*y+x = 0 := by
    have hh := canonicalAChartQuadratic25_root_equation K π
    dsimp only at hh
    simpa only [hz, _root_.map_zero, mul_zero, zero_mul, zero_sub, zero_pow (by decide : 2 ≠ 0),
      add_zero, zero_add, neg_zero, sub_zero, neg_mul, sub_eq_add_neg] using hh
  have hprod : y*(x-y) = x := by linear_combination -hq
  have hym : IsRegular y :=
    (show IsRegular (y*(x-y)) from hprod.symm ▸ hxm).of_mul_left
  have he := canonicalAChartLinearRemainder25_mk K π
  dsimp only at he
  rw [he]
  simpa only [hz, _root_.map_zero, mul_zero, zero_mul, zero_add, add_zero] using hxm.mul hym

end N25
