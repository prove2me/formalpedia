-- Prove2me | solution 1 for JacobianCounterexample.jacobianDet_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:06.375554+00:00
-- url     : https://prove2.me/submissions/c50066ee-c9c3-4ce8-ac49-64d1cc4b5c3c

import Definitions.Def_JacobianConjecture_Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_JacobianConjecture_Proof

set_option autoImplicit true
noncomputable section
open Matrix Function
open MvPolynomial
open JacobianCounterexample
variable (K : Type*) [Field K]
namespace JacobianCounterexample
theorem _root_.solution : MvPolynomial.jacobianDet (F K) = C (-2) := by
  simp only [MvPolynomial.jacobianDet, MvPolynomial.jacobianMatrix,
    det_fin_three, Matrix.of_apply, F, cons_val_zero, cons_val_one,
    cons_val_two, head_cons, tail_cons, map_add, map_sub,
    Derivation.map_one_eq_zero, pderiv_mul, pderiv_pow, pderiv_C,
    pderiv_X_self, pderiv_X_of_ne, ne_eq, Fin.reduceEq,
    not_false_eq_true]
  simp only [map_neg, map_ofNat]
  ring
end JacobianCounterexample
