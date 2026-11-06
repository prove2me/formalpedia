-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.reductionMultiplicity_mul_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:27:55.828952+00:00
-- url     : https://prove2.me/submissions/6305e231-abef-4661-82f8-329a661199f5

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_sum_reduction

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (π : A →+* B) (hπ : Function.Surjective π) :
    reductionMultiplicity π * Fintype.card B = Fintype.card A := by
  have h := sum_reduction π hπ (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h.symm
end OAI.SevenEighths.CenteredMomentCorrelation
