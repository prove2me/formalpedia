-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.shiftCorrelation_nonprincipal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:08.00098+00:00
-- url     : https://prove2.me/submissions/65ff0363-9e8b-4b85-af17-266e46b67305

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
theorem _root_.solution (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    {k : F} (hk : k ≠ 0) : shiftCorrelation χ k = -1 := by
  rw [shiftCorrelation_scale χ hk, shiftCorrelation_one, jacobiSum_nontrivial_inv hχ,
    mul_neg, ← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr one_ne_zero))]
end OAI.SevenEighths.CenteredMomentCorrelation
