-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_unit_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:56.472789+00:00
-- url     : https://prove2.me/submissions/ac6f8d62-09f9-4048-a6d6-a30a6031bb09

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
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (u : Aˣ) (v k : A) (f g : A → ℂ) :
    fullCorrelation (fun x => v * x) (fun y => (u : A) * y) f g k =
      ∑ x : A, f x * star (g ((↑u⁻¹ : A) * (v * x - k))) := by
  classical
  have hsolve (x y : A) : v * x - (u : A) * y = k ↔
      y = (↑u⁻¹ : A) * (v * x - k) := by
    constructor
    · intro h
      have heq : v * x - k = (u : A) * y := by linear_combination h
      rw [heq, ← mul_assoc, Units.inv_mul, one_mul]
    · intro h
      rw [h, ← mul_assoc, Units.mul_inv, one_mul]
      ring
  simp only [fullCorrelation, hsolve, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
end OAI.SevenEighths.CenteredMomentCorrelation
