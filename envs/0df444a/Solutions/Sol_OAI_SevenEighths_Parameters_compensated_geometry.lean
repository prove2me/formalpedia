-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.compensated_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:18:29.764298+00:00
-- url     : https://prove2.me/submissions/89b5c13c-9a06-4045-8323-cb7786277e89

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_Parameters

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.Parameters
namespace OAI.SevenEighths.Parameters
theorem _root_.solution {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · norm_num
end OAI.SevenEighths.Parameters
