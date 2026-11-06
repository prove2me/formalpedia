-- Prove2me | solution 1 for OAI.SevenEighths.Endpoint.denominator_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:20.575197+00:00
-- url     : https://prove2.me/submissions/646715c9-a8da-4826-b532-c305690a16e7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Endpoint
noncomputable section
namespace OAI.SevenEighths.Endpoint
theorem _root_.solution {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ denominator y ∧ denominator y ≤ 3 := by
  dsimp [denominator]
  constructor <;> linarith
end OAI.SevenEighths.Endpoint
