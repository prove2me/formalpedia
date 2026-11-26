-- Prove2me | solution 1 for JacobianCounterexample.not_jacobian_conjecture_complex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:41.120888+00:00
-- url     : https://prove2.me/submissions/502048b7-d819-4ee0-8c9c-01b567e60bfa

import Definitions.Def_JacobianConjecture_Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_JacobianConjecture_Proof
import Theorems.Thm_JacobianCounterexample_jacobianDet_F
import Theorems.Thm_JacobianCounterexample_evalMap_F_p1
import Theorems.Thm_JacobianCounterexample_evalMap_F_p2

set_option autoImplicit true
noncomputable section
open Matrix Function
open MvPolynomial
open JacobianCounterexample
variable (K : Type*) [Field K]
variable {K}
namespace JacobianCounterexample
theorem _root_.solution :
    ¬ ∀ P : Fin 3 → MvPolynomial (Fin 3) ℂ,
      IsUnit (MvPolynomial.jacobianDet P) →
        Injective (MvPolynomial.evalMap P) := by
  intro h
  have hunit : IsUnit (MvPolynomial.jacobianDet (F ℂ)) := by
    rw [jacobianDet_F]
    exact (isUnit_iff_ne_zero.mpr
      (neg_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0))).map C
  have h12 : (![1, -(3 / 2), 13 / 2] : Fin 3 → ℂ) =
      ![-1, 3 / 2, 13 / 2] :=
    h (F ℂ) hunit
      ((evalMap_F_p1 (K := ℂ) (by norm_num)).trans
        (evalMap_F_p2 (K := ℂ) (by norm_num)).symm)
  have h0 : (1 : ℂ) = -1 := congrFun h12 0
  norm_num at h0
end JacobianCounterexample
