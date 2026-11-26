-- Prove2me | solution 1 for JacobianCounterexample.explicit_three_point_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T07:59:40.741572+00:00
-- url     : https://prove2.me/submissions/403ffa49-e3fd-45f7-9c4f-917e905dc88d

import Definitions.Def_JacobianConjecture_Definitions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_JacobianConjecture_Proof
import Theorems.Thm_JacobianCounterexample_evalMap_F_p0
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
    MvPolynomial.evalMap (F ℂ) ![0, 0, -(1 / 4)] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (F ℂ) ![1, -(3 / 2), 13 / 2] = ![-(1 / 4), 0, 0] ∧
      MvPolynomial.evalMap (F ℂ) ![-1, 3 / 2, 13 / 2] = ![-(1 / 4), 0, 0] := by
  exact ⟨evalMap_F_p0 (K := ℂ),
    ⟨evalMap_F_p1 (K := ℂ) (by norm_num),
      evalMap_F_p2 (K := ℂ) (by norm_num)⟩⟩
end JacobianCounterexample
