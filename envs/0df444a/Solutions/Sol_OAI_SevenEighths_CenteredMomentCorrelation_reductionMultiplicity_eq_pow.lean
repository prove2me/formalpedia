-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.reductionMultiplicity_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:46.395246+00:00
-- url     : https://prove2.me/submissions/cfb6b5e2-660d-43f8-aa6d-a9c3bd37af08

import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.GroupTheory.Index
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_reductionMultiplicity_mul_card

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (π : A →+* B) (hπ : Function.Surjective π)
    {P c : ℕ} (hP : 0 < P) (hc : 1 ≤ c)
    (hA : Fintype.card A = P ^ c) (hB : Fintype.card B = P) :
    reductionMultiplicity π = P ^ (c - 1) := by
  apply Nat.eq_of_mul_eq_mul_right hP
  rw [← hB, reductionMultiplicity_mul_card π hπ, hA, hB, ← pow_succ,
    Nat.sub_add_cancel hc]
end OAI.SevenEighths.CenteredMomentCorrelation
