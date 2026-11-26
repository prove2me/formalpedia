-- Prove2me | solution 1 for JacobianCounterexample.evalMap_F_p1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:05.348527+00:00
-- url     : https://prove2.me/submissions/51fa7f05-c0f2-429f-a357-c2f07a45a123

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
variable {K}
namespace JacobianCounterexample
theorem _root_.solution (h2 : (2 : K) ≠ 0) :
    MvPolynomial.evalMap (F K) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] := by
  have h4 : (4 : K) ≠ 0 :=
    (by norm_num : (2 : K) * 2 = 4) ▸ mul_ne_zero h2 h2
  funext i
  fin_cases i <;> simp [MvPolynomial.evalMap, F] <;> field_simp [h4] <;> ring
end JacobianCounterexample
