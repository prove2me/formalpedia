-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.coefficient_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:41:09.27903+00:00
-- url     : https://prove2.me/submissions/249f59d0-bf5f-4e8b-97ec-8dd927b083bc

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_normTwist_mul
attribute [local simp] OAI.SevenEighths.CenteredMoment.ofResidueMask_keep_one
attribute [local simp] OAI.SevenEighths.CenteredMoment.MaskedCharacter.value_mul
attribute [local simp] OAI.SevenEighths.CenteredMoment.normTwist_mul

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution (d : MaskedCharacter M R) (N : M →* ℝ≥0)
    (t : ℝ) (a b : M) :
    coefficient d N t (a * b) = coefficient d N t a * coefficient d N t b := by
  simp only [coefficient, MaskedCharacter.value_mul, normTwist_mul]
  ring
end OAI.SevenEighths.CenteredMoment
