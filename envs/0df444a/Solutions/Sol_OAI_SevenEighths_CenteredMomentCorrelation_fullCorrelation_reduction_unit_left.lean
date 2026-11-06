-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_reduction_unit_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:28.744083+00:00
-- url     : https://prove2.me/submissions/593db901-416c-4835-970e-1bdf9d5c3fd3

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_swap
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_reduction_unit_right

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (π : A →+* B)
    (hπ : Function.Surjective π) (u : A) (v : Aˣ) (k : A) (f g : B → ℂ) :
    fullCorrelation (fun x : A => (v : A) * x) (fun y : A => u * y)
        (fun x => f (π x)) (fun y => g (π y)) k =
      (reductionMultiplicity π : ℂ) *
        fullCorrelation (fun x : B => π v * x) (fun y : B => π u * y) f g (π k) := by
  rw [fullCorrelation_swap, fullCorrelation_reduction_unit_right π hπ v u (-k) g f]
  rw [fullCorrelation_swap (fun x : B => π v * x) (fun y : B => π u * y) f g (π k)]
  simp only [map_neg, star_mul, star_natCast]
  ring
end OAI.SevenEighths.CenteredMomentCorrelation
