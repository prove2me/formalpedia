-- Prove2me | solution 1 for JacobianCounterexample.evalMap_F_p0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:06.920734+00:00
-- url     : https://prove2.me/submissions/9f7b7820-b06a-4525-9706-9cf1febf44fa

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
theorem _root_.solution :
    MvPolynomial.evalMap (F K) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] := by
  funext i
  fin_cases i <;> simp [MvPolynomial.evalMap, F]
end JacobianCounterexample
