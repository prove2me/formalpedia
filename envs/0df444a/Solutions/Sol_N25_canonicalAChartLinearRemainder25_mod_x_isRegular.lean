-- Prove2me | solution 1 for N25.canonicalAChartLinearRemainder25_mod_x_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:58.730092+00:00
-- url     : https://prove2.me/submissions/17753b26-2173-476a-a36b-f3d38f746523

import Mathlib
import Theorems.Thm_N25_canonicalAChartQuadratic25_monic
import Definitions.Def_N25_CanonicalAChartTower
import Theorems.Thm_N25_isRegular_algebraMap_adjoinRoot_of_monic
import Theorems.Thm_N25_canonicalAChartLinearRemainder25_mk
import Theorems.Thm_N25_canonicalAChartBase_constant_not_mem_x
import Theorems.Thm_N25_canonicalAChartQuadratic25_root_equation

/-! Coordinate regularity in the monic presentation of the canonical A-chart. -/
noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

local instance xSpecialization_semiring_se5bc96 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

/-- Setting x=0 leaves the cubic regular in the monic quadric extension. -/
theorem _root_.solution :
    let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸
      Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))) :=
      Ideal.Quotient.mk _
    IsRegular (AdjoinRoot.mk ((canonicalAChartQuadratic25 K).map π)
      ((canonicalAChartLinearRemainder25 K).map π)) := by
  dsimp only
  let I := Ideal.span ({canonicalAChartBaseX25 K} : Set (CanonicalAChartBase25 K))
  let π : CanonicalAChartBase25 K →+* (CanonicalAChartBase25 K ⧸ I) := Ideal.Quotient.mk I
  have hIp : I.IsPrime := (Ideal.span_singleton_prime X_ne_zero).mpr (prime_X (R := Polynomial K))
  letI : IsDomain (CanonicalAChartBase25 K ⧸ I) := (Ideal.Quotient.isDomain_iff_prime I).mpr hIp
  let q := (canonicalAChartQuadratic25 K).map π
  let ι := AdjoinRoot.of q
  let y := AdjoinRoot.root q
  let z := ι (π (canonicalAChartBaseZ25 K))
  have hx : π (canonicalAChartBaseX25 K) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hz : π (canonicalAChartBaseZ25 K) ≠ 0 := by
    intro h
    exact canonicalAChartBase_constant_not_mem_x K X X_ne_zero
      (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hz1 : π (canonicalAChartBaseZ25 K)-1 ≠ 0 := by
    intro h
    apply canonicalAChartBase_constant_not_mem_x K (X-1) (monic_X_sub_C 1).ne_zero
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [Polynomial.map_sub, Polynomial.map_one, canonicalAChartBaseZ25,
      _root_.map_sub, _root_.map_one] using h
  have hzm : IsRegular z := isRegular_algebraMap_adjoinRoot_of_monic
    q ((canonicalAChartQuadratic25_monic K).map π) hz
  have hzm1 : IsRegular (z-1) := by
    have hh := isRegular_algebraMap_adjoinRoot_of_monic
      q ((canonicalAChartQuadratic25_monic K).map π) hz1
    simpa only [AdjoinRoot.algebraMap_eq, z, ι, _root_.map_sub, _root_.map_one] using hh
  have hq : (y+z)^2 = z := by
    have hh := canonicalAChartQuadratic25_root_equation K π
    dsimp only at hh
    have hh' : y^2+2*z*y+z^2-z = 0 := by
      simpa only [hx, _root_.map_zero, sub_zero, zero_mul, mul_zero, add_zero] using hh
    linear_combination hh'
  have hprod : (y+z-1)*(y+z+1) = z-1 := by linear_combination hq
  have hym : IsRegular (y+z-1) :=
    (show IsRegular ((y+z-1)*(y+z+1)) from hprod.symm ▸ hzm1).of_mul_left
  have he := canonicalAChartLinearRemainder25_mk K π
  dsimp only at he
  rw [he]
  have he' :
      (ι (π (canonicalAChartBaseX25 K))*z+ι (π (canonicalAChartBaseX25 K))+z)*y+
      z*(z-1-ι (π (canonicalAChartBaseX25 K))^2) = z*(y+z-1) := by
    simp only [hx, _root_.map_zero, zero_mul, zero_add, zero_pow (by decide : 2 ≠ 0), sub_zero]
    ring
  change IsRegular ((ι (π (canonicalAChartBaseX25 K))*z+ι (π (canonicalAChartBaseX25 K))+z)*y+
      z*(z-1-ι (π (canonicalAChartBaseX25 K))^2))
  rw [he']
  exact hzm.mul hym

local instance zSpecialization_semiring_se5bc96 : Semiring (CanonicalAChartBase25 K ⧸
    Ideal.span ({canonicalAChartBaseZ25 K} : Set (CanonicalAChartBase25 K))) :=
  (Ideal.Quotient.commRing _).toSemiring

end N25
