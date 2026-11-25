-- Prove2me | solution 1 for GroundTheory.Global.coe_derivative_charpolyRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:23:24.521803+00:00
-- url     : https://prove2.me/submissions/b815626e-efd6-4d59-bb6f-7ad497ff7df8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Theorems.Thm_GroundTheory_Global_one_sub_X_smul_mul_matrixGeomSeries
import Theorems.Thm_GroundTheory_Global_trace_matrixGeomSeries_mul
import Theorems.Thm_GroundTheory_Global_coe_charpolyRev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace GroundTheory.Global
theorem _root_.solution (M : Matrix n n R) :
    ((derivative M.charpolyRev : R[X]) : PowerSeries R) =
      -(M.charpolyRev : PowerSeries R) * PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  set T : PowerSeries R := PowerSeries.X
  set N : Matrix n n (PowerSeries R) := M.map PowerSeries.C
  set A : Matrix n n (PowerSeries R) := 1 - T • N
  set B := matrixGeomSeries M
  have hAB : A * B = 1 := one_sub_X_smul_mul_matrixGeomSeries M

  set ψ : R[X] →+* (PowerSeries R)[X] :=
    (Polynomial.compRingHom (Polynomial.C T + Polynomial.X)).comp
      (Polynomial.mapRingHom PowerSeries.C)
  have hψ : ∀ p : R[X], ψ p = (p.map PowerSeries.C).comp (Polynomial.C T + Polynomial.X) :=
    fun p => rfl
  have hfac : ψ M.charpolyRev =
      Polynomial.C A.det * (1 + (Polynomial.X : (PowerSeries R)[X]) •
        (-(B * N)).map Polynomial.C).det := by
    rw [Matrix.charpolyRev, RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    have h1 : A.map Polynomial.C * (1 + (Polynomial.X : (PowerSeries R)[X]) •
        (-(B * N)).map Polynomial.C) =
        A.map Polynomial.C - (Polynomial.X : (PowerSeries R)[X]) • N.map Polynomial.C := by
      rw [mul_add, mul_one, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_neg,
        ← Matrix.mul_assoc, hAB, Matrix.one_mul, Matrix.map_neg _ (map_neg Polynomial.C), smul_neg, sub_eq_add_neg]
    rw [show (Polynomial.C : PowerSeries R →+* (PowerSeries R)[X]).mapMatrix A =
      A.map Polynomial.C from rfl, h1]
    ext i j
    by_cases h : i = j <;>
      simp [hψ, A, N, T, h] <;> ring
  have hder : (derivative (ψ M.charpolyRev)).eval 0 =
      ((derivative M.charpolyRev : R[X]) : PowerSeries R) := by
    rw [hψ, Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_add, one_mul, Polynomial.eval_comp, Polynomial.derivative_map,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, add_zero, Polynomial.eval_map,
      Polynomial.eval₂_C_X_eq_coe]
  rw [← hder, hfac, Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Matrix.derivative_det_one_add_X_smul, Matrix.trace_neg, ← coe_charpolyRev,
    ← trace_matrixGeomSeries_mul, mul_neg, neg_mul]
end GroundTheory.Global
