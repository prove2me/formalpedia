-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.shiftCorrelation_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:09.858193+00:00
-- url     : https://prove2.me/submissions/cb80ad3b-ed85-4b3d-bfde-ce99b7b1d4d0

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_shiftCorrelation_scale
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_shiftCorrelation_one

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution {k : F} (hk : k ≠ 0) :
    shiftCorrelation (1 : MulChar F ℂ) k = (Fintype.card F : ℂ) - 2 := by
  rw [shiftCorrelation_scale _ hk, shiftCorrelation_one, inv_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero)), one_mul, jacobiSum_one_one]
end OAI.SevenEighths.CenteredMomentCorrelation
