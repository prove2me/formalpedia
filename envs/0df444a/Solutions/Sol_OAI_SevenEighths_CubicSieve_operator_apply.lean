-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.operator_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:21.969556+00:00
-- url     : https://prove2.me/submissions/cba5f5e1-fcb8-47ec-9fdf-988d7ea58527

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Operator

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
omit [DecidableEq m]
namespace OAI.SevenEighths.CubicSieve
theorem _root_.solution (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl
end OAI.SevenEighths.CubicSieve
