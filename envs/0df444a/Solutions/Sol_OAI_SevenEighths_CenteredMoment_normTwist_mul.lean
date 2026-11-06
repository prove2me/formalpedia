-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.normTwist_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:36.425705+00:00
-- url     : https://prove2.me/submissions/17f3f798-25b9-4401-b6a4-4e610b9c656c

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_ofResidueMask_keep_one
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_MaskedCharacter_value_mul
attribute [local simp] OAI.SevenEighths.CenteredMoment.ofResidueMask_keep_one
attribute [local simp] OAI.SevenEighths.CenteredMoment.MaskedCharacter.value_mul

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution (N : M →* ℝ≥0) (t : ℝ) (a b : M) :
    normTwist N t (a * b) = normTwist N t a * normTwist N t b := by
  simp only [normTwist, map_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (N a).coe_nonneg (N b).coe_nonneg _
end OAI.SevenEighths.CenteredMoment
