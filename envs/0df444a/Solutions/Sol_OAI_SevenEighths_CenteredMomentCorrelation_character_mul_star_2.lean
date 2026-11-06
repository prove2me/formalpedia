-- Prove2me | solution 2 for OAI.SevenEighths.CenteredMomentCorrelation.character_mul_star
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:31.959797+00:00
-- url     : https://prove2.me/submissions/aaf8d470-c38e-4177-a64d-4d3544623f05

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {F : Type*} [Field F] [Fintype F]
theorem OA1Aux.character_mul_star {F : Type*} [Field F] [Fintype F] (χ : MulChar F ℂ) {a : F}
    (ha : a ≠ 0) : χ a * star (χ a) = 1 := by
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  obtain ⟨u, rfl⟩ := Ne.isUnit ha
  exact MulChar.one_apply_coe u

theorem solution (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * star (χ a) = 1 := by
  exact OA1Aux.character_mul_star χ ha
