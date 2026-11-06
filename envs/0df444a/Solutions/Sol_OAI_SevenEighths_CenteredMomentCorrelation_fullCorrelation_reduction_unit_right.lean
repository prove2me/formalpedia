-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_reduction_unit_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:45.749972+00:00
-- url     : https://prove2.me/submissions/4e0641aa-d8f0-420a-8793-3dc6380ec5c2

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_sum_reduction
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_unit_right

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (π : A →+* B)
    (hπ : Function.Surjective π) (u : Aˣ) (v k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => v * x) (fun y : A => (u : A) * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_unit_right]
  have hright := fullCorrelation_unit_right (Units.map π.toMonoidHom u) (π v) (π k) f g
  change fullCorrelation _ (fun y : B => π u * y) _ _ _ = _ at hright
  rw [hright]
  change (∑ x : A, f (π x) * star (g (π ((↑u⁻¹ : A) * (v * x - k))))) =
    (reductionMultiplicity π : ℂ) *
      ∑ x : B, f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k)))
  simpa only [map_mul, map_sub] using
    sum_reduction π hπ (fun x => f x * star (g (π (↑u⁻¹ : A) * (π v * x - π k))))
end OAI.SevenEighths.CenteredMomentCorrelation
