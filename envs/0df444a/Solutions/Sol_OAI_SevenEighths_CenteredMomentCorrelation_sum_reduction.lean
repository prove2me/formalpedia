-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.sum_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:11.501222+00:00
-- url     : https://prove2.me/submissions/ab320bb6-3eeb-4606-ac8e-b85c12eb8a4c

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
theorem _root_.solution (π : A →+* B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ x : A, f (π x)) = (reductionMultiplicity π : ℂ) * ∑ y : B, f y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π (fun x => f (π x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = ∑ x : A with π x = y, f y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by
      have hc := AddMonoidHom.card_fiber_eq_of_mem_range π (hπ y) (hπ 0)
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hc]
      rfl
end OAI.SevenEighths.CenteredMomentCorrelation
