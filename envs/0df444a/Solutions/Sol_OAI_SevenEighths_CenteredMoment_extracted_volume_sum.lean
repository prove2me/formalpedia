-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.extracted_volume_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:34.689119+00:00
-- url     : https://prove2.me/submissions/ca4cc6bf-0177-44db-8143-62e236728daa

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
import Theorems.Thm_OAI_SevenEighths_CenteredMoment_extracted_volume_phase

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution {D : Type*} (s : Finset D) (a : D → ℂ)
    (norm : D → ℝ) (hnorm : ∀ d ∈ s, 0 < norm d)
    (c I : ℂ) (t X : ℝ) (hX : 0 ≤ X) :
    (∑ d ∈ s, a d * (norm d : ℂ) ^ (Complex.I * t) *
      volumeTerm c I t (X / norm d)) =
      volumeTerm (c * ∑ d ∈ s, a d / (norm d : ℂ)) I t X := by
  unfold volumeTerm
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have h := extracted_volume_phase X (norm d) t hX (hnorm d hd)
  calc
    _ = a d * c * I * ((norm d : ℂ) ^ (Complex.I * t) *
        ((X / norm d : ℝ) : ℂ) ^ (1 + Complex.I * t)) := by ring
    _ = _ := by rw [h]; ring
end OAI.SevenEighths.CenteredMoment
