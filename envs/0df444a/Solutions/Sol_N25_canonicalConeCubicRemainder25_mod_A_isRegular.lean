-- Prove2me | solution 1 for N25.canonicalConeCubicRemainder25_mod_A_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:37:28.127214+00:00
-- url     : https://prove2.me/submissions/0992c20a-f3ca-4155-84c0-07b3d09f7b49

import Mathlib
import Definitions.Def_N25_CanonicalConeTower
import Theorems.Thm_N25_isRegular_algebraMap_adjoinRoot_of_monic
import Definitions.Def_N25_CanonicalConeBoundary
import Theorems.Thm_N25_canonicalConeBoundaryMap25_X_ne_zero
import Theorems.Thm_N25_canonicalConeBoundaryMap25_Z_ne_zero
import Theorems.Thm_N25_canonicalConeBoundaryMap25_A
import Theorems.Thm_N25_canonicalConeQuadricPolynomial25_monic

/-! Regularity of the normalizing linear form in the monic cone presentation. -/

noncomputable section

namespace N25

open Polynomial

variable (K : Type*) [Field K]

/-- Modulo A, the cubic is a product of regular scalars and x-y. -/
theorem _root_.solution :
    IsRegular (AdjoinRoot.mk
      ((canonicalConeQuadricPolynomial25 K).map (canonicalConeBoundaryMap25 K))
      ((canonicalConeCubicRemainder25 K).map (canonicalConeBoundaryMap25 K))) := by
  let π := canonicalConeBoundaryMap25 K
  let q := (canonicalConeQuadricPolynomial25 K).map π
  let x := π (canonicalConeBaseX25 K)
  let z := π (canonicalConeBaseZ25 K)
  let y := AdjoinRoot.root q
  let m := AdjoinRoot.of q
  have hq : q.Monic := (canonicalConeQuadricPolynomial25_monic K).map π
  have hx : x ≠ 0 := canonicalConeBoundaryMap25_X_ne_zero K
  have hz : z ≠ 0 := canonicalConeBoundaryMap25_Z_ne_zero K
  have hrz : IsRegular (m z) := isRegular_algebraMap_adjoinRoot_of_monic q hq hz
  have hrx : IsRegular (m (-x)) := isRegular_algebraMap_adjoinRoot_of_monic q hq (neg_ne_zero.mpr hx)
  have he : q = X^2+C (2*z-x)*X+C (z^2-2*x*z) := by
    simp [q, canonicalConeQuadricPolynomial25, π, x, z, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, canonicalConeBoundaryMap25_A, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat]
    simp only [_root_.map_add (canonicalConeBoundaryMap25 K), _root_.map_sub (canonicalConeBoundaryMap25 K),
      _root_.map_mul (canonicalConeBoundaryMap25 K), _root_.map_pow (canonicalConeBoundaryMap25 K),
      _root_.map_ofNat (canonicalConeBoundaryMap25 K), _root_.map_add, _root_.map_sub,
      _root_.map_mul, _root_.map_pow, _root_.map_ofNat]
  have hprod : (m x-y)*(y+2*m z) = (m z)^2 := by
    have hp : (X-C x)*(X+C (2*z)) = q-C (z^2) := by
      rw [he]
      simp only [_root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, _root_.map_ofNat]
      ring
    have hm := congrArg (AdjoinRoot.mk q) hp
    simp only [_root_.map_sub, _root_.map_mul, _root_.map_add, _root_.map_pow, AdjoinRoot.mk_self, zero_sub,
      AdjoinRoot.mk_C, AdjoinRoot.mk_X, _root_.map_ofNat] at hm
    change (y-m x)*(y+2*m z) = -(m z)^2 at hm
    calc
      _ = -((y-m x)*(y+2*m z)) := by ring
      _ = _ := by rw [hm]; ring
  have hrxy : IsRegular (m x-y) := (isRegular_mul_iff.mp (hprod.symm ▸ hrz.pow 2)).1
  have hc : AdjoinRoot.mk q ((canonicalConeCubicRemainder25 K).map π) = m (-x)*m z*(m x-y) := by
    simp only [canonicalConeCubicRemainder25, Polynomial.map_add, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    simp only [π, canonicalConeBoundaryMap25_A, _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow, zero_mul, mul_zero,
      zero_add, add_zero, zero_sub, zero_pow (by decide : 2 ≠ 0)]
    simp only [AdjoinRoot.mk_C, AdjoinRoot.mk_X, _root_.map_mul, _root_.map_sub, _root_.map_neg, _root_.map_pow]
    change m x * m z * y + m (π (canonicalConeBaseA25 K * canonicalConeBaseZ25 K ^ 2 -
      canonicalConeBaseA25 K ^ 2 * canonicalConeBaseZ25 K - canonicalConeBaseX25 K ^ 2 * canonicalConeBaseZ25 K)) =
      -m x * m z * (m x-y)
    simp only [_root_.map_sub, _root_.map_mul, _root_.map_pow, π, canonicalConeBoundaryMap25_A, zero_mul, mul_zero,
      zero_pow (by decide : 2 ≠ 0), zero_sub, sub_zero]
    simp only [_root_.map_sub (canonicalConeBoundaryMap25 K), _root_.map_mul (canonicalConeBoundaryMap25 K),
      _root_.map_pow (canonicalConeBoundaryMap25 K), canonicalConeBoundaryMap25_A, zero_mul, mul_zero,
      zero_pow (by decide : 2 ≠ 0), zero_sub, sub_zero, _root_.map_neg m, _root_.map_mul m, _root_.map_pow m]
    change m x * m z * y + -(m x ^ 2 * m z) = -m x * m z * (m x-y)
    ring
  rw [hc]
  exact (hrx.mul hrz).mul hrxy

end N25
