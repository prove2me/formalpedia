-- Prove2me | solution 1 for KernelRank.eq_zero_of_shiftDeriv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:29:35.974171+00:00
-- url     : https://prove2.me/submissions/949d4cd0-7e6e-4fed-80d9-e16050a30dad

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution {a μ : ℂ} (hμ : μ ≠ a) {P : ℂ[X]}
    (h : shiftDeriv a μ P = 0) : P = 0 := by
  by_contra hP
  have hcoeff := congrArg (fun Q => Q.coeff P.natDegree) h
  simp only [shiftDeriv, coeff_add, coeff_derivative, coeff_C_mul, coeff_zero] at hcoeff
  rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul, zero_add] at hcoeff
  exact mul_ne_zero (sub_ne_zero.mpr hμ) (leadingCoeff_ne_zero.mpr hP) hcoeff
end KernelRank
