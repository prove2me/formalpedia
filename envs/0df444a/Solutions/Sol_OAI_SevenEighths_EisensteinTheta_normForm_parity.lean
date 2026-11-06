-- Prove2me | solution 1 for OAI.SevenEighths.EisensteinTheta.normForm_parity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:19.943061+00:00
-- url     : https://prove2.me/submissions/b5e8d0eb-8e11-457b-8335-42f9a5e50f29

import Definitions.Def_OAI_NumberTheory_DirichletL_ThetaProduct
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MeasureTheory
open OAI.SevenEighths OAI.SevenEighths.EisensteinTheta
open ThetaProduct
namespace OAI.SevenEighths.EisensteinTheta
theorem _root_.solution (a b L : ℝ) (hL : L ≠ 0) (e : Fin 2) (i j : ℤ) :
    normForm (a + L * (i + j)) (b + L * (2 * j + e)) =
      L ^ 2 * (i + xShift a b L e) ^ 2 +
        (3 * L ^ 2) * (j + yShift b L e) ^ 2 := by
  unfold normForm xShift yShift
  field_simp
  ring
end OAI.SevenEighths.EisensteinTheta
