-- Prove2me | solution 1 for HodgeComputer.Formal.QuadraticCovers.simplePole_residue
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T03:33:34.699822+00:00
-- url     : https://prove2.me/submissions/819e535b-a0ec-4be1-bab6-8f5968500afd

import Definitions.Def_HodgeComputerFormal_RationalResidues
import Mathlib.Tactic

set_option autoImplicit false
open CrossedRationalResidue Polynomial
open scoped Polynomial

theorem solution
    {K : Type*} [Field K] (P Q : K[X]) (a : K)
    (hQ0 : Q.eval a = 0) (hQd : Q.derivative.eval a ≠ 0) :
    CrossedRationalResidue.residue a
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) =
    P.eval a / Q.derivative.eval a := by
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hQ0
  have hR_eval : R.eval a = Q.derivative.eval a := by
    have hd := congrArg (fun f : K[X] => f.derivative.eval a) hR
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
      one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hd
    exact hd.symm
  have hRne : R.eval a ≠ 0 := hR_eval.symm ▸ hQd
  have hEq : algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q =
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) R) / uniformizer a := by
    rw [hR, map_mul, uniformizer]
    have hu := uniformizer_ne_zero a
    have hR0 : algebraMap K[X] (RatFunc K) R ≠ 0 :=
      polynomialMap_ne_zero (fun h => hRne (by simp [h]))
    field_simp [hu, hR0]
  rw [hEq, residue_div_uniformizer, valueAt_div_polynomials a P R hRne, hR_eval]
