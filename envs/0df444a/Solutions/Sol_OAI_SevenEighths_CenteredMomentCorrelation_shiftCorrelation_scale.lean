-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.shiftCorrelation_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:26.890322+00:00
-- url     : https://prove2.me/submissions/87b41c50-613f-4dea-b1cc-f4704533119f

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_character_mul_star

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (χ : MulChar F ℂ) {k : F} (hk : k ≠ 0) :
    shiftCorrelation χ k = shiftCorrelation χ 1 := by
  unfold shiftCorrelation
  rw [← (Equiv.mulLeft₀ k hk).sum_comp]
  swap
  · simp
  apply Finset.sum_congr rfl
  intro x _
  simp only [Equiv.mulLeft₀_apply]
  rw [show k * x - k = k * (x - 1) by ring, map_mul, map_mul, star_mul]
  calc
    _ = (χ k * star (χ k)) * (χ x * star (χ (x - 1))) := by ring
    _ = _ := by rw [character_mul_star χ hk, one_mul]
end OAI.SevenEighths.CenteredMomentCorrelation
