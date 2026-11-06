-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.extracted_volume_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:00.713252+00:00
-- url     : https://prove2.me/submissions/169a40f9-eefc-4be7-9911-000cf8c05fb8

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
theorem _root_.solution (X D t : ℝ) (hX : 0 ≤ X) (hD : 0 < D) :
    (D : ℂ) ^ (Complex.I * t) * ((X / D : ℝ) : ℂ) ^ (1 + Complex.I * t) =
      (X : ℂ) ^ (1 + Complex.I * t) / (D : ℂ) := by
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hD)
  have hp : (D : ℂ) ^ (Complex.I * t) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hDc)
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hX hD.le,
    Complex.cpow_add _ _ hDc, Complex.cpow_one]
  field_simp
end OAI.SevenEighths.CenteredMoment
