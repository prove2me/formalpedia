-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.MaskedCharacter.value_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:35:27.720193+00:00
-- url     : https://prove2.me/submissions/ab5ef66c-1eb5-4d49-bcda-14a4b2e6c5cc

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
attribute [local simp] OAI.SevenEighths.CenteredMoment.ofResidueMask_keep_one

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
namespace MaskedCharacter
theorem _root_.solution (d : MaskedCharacter M R) (a b : M) :
    d.value (a * b) = d.value a * d.value b := by
  classical
  simp only [MaskedCharacter.value, d.keep_mul, map_mul]
  split_ifs <;> simp_all
end MaskedCharacter
end OAI.SevenEighths.CenteredMoment
