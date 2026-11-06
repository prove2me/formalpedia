-- Prove2me | solution 1 for OAI.SevenEighths.Endpoint.primeWeight_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:58:23.913359+00:00
-- url     : https://prove2.me/submissions/d28658ca-17a8-403a-ae04-5c7dbc8112e0

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
    7 / 9 ≤ primeWeight y ∧ primeWeight y ≤ 2 := by
  have hs := sq_nonneg y
  have ht := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  dsimp [primeWeight]
  constructor <;> nlinarith
end OAI.SevenEighths.Endpoint
