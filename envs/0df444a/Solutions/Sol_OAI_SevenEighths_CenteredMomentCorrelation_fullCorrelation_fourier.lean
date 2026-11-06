-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:48.517746+00:00
-- url     : https://prove2.me/submissions/32529f24-668f-4edc-9c05-7a4ff15b88b6

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
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (j : R) :
    (∑ h : R, fourierSum ψ left f h * star (fourierSum ψ right g h) * ψ (-(h * j))) =
      (Fintype.card R : ℂ) * fullCorrelation left right f g j := by
  classical
  simp only [fourierSum, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  have hphase (h : R) (x : X) (y : Y) :
      (f x * ψ (h * left x) * (star (ψ (h * right y)) * star (g y))) * ψ (-(h * j)) =
        (f x * star (g y)) * ψ (h * (left x - right y - j)) := by
    have hs : star (ψ (h * right y)) = ψ (-(h * right y)) := by
      simpa only [← starRingEnd_apply] using (AddChar.map_neg_eq_conj ψ (h * right y)).symm
    rw [hs]
    calc
      _ = (f x * star (g y)) *
          (ψ (h * left x) * ψ (-(h * right y)) * ψ (-(h * j))) := by ring
      _ = _ := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
        congr 2
        ring
  simp_rw [hphase, ← Finset.mul_sum, AddChar.sum_mulShift _ hψ]
  simp only [fullCorrelation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : left x - right y = j
  · simp [hxy, mul_comm]
  · simp [sub_ne_zero.mpr hxy, hxy]
end OAI.SevenEighths.CenteredMomentCorrelation
