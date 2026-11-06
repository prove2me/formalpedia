-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.scale_le_product_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:59.207643+00:00
-- url     : https://prove2.me/submissions/fde1d536-cc0f-4cfc-8e4d-1c9bad3307cc

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Basic

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution {X Y T L : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hY : L ≤ Y) (hprod : X * Y = T) :
    X ≤ T / L := by
  apply (le_div_iff₀ hL).mpr
  rw [← hprod]
  exact mul_le_mul_of_nonneg_left hY hX
end OAI.SevenEighths.CenteredMoment
