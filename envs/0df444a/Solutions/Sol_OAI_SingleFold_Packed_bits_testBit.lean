-- Prove2me | solution 1 for OAI.SingleFold.Packed.bits_testBit
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:10:33.091318+00:00
-- url     : https://prove2.me/submissions/74f9bfa6-6772-487a-8b8f-07a04842215c

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed

open OAI OAI.SingleFold OAI.SingleFold.Packed


theorem solution (x y : ℕ) : Bits x y ↔ ∀ i, x.testBit i=true → y.testBit i=true := by
  unfold Bits
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
  refine forall_congr' (fun i => ?_)
  have h1 := Nat.mod_lt (x/2^i) (show 0 < 2 by norm_num)
  have h2 := Nat.mod_lt (y/2^i) (show 0 < 2 by norm_num)
  omega

