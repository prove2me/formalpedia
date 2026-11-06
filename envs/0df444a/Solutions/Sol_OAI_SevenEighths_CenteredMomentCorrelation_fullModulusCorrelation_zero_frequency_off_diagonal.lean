-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullModulusCorrelation_zero_frequency_off_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:25.546133+00:00
-- url     : https://prove2.me/submissions/bd2026b8-3539-41b8-8dba-ea7da16b7bd2

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_congruence
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_zero_frequency_units_force_divides
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ)
    (hne : Ideal.span ({u} : Set A) ≠ Ideal.span ({v} : Set A)) :
    fullModulusCorrelation u v χu χv 0 = 0 := by
  classical
  unfold fullModulusCorrelation fullCorrelation
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  refine Quotient.inductionOn₂' x y ?_
  intro a b
  change (if scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) a) -
      scaledResidue v u (u * v) (mul_comm u v) (Ideal.Quotient.mk (Ideal.span {v}) b) =
      Ideal.Quotient.mk (Ideal.span {u * v}) 0
    then χu (Ideal.Quotient.mk (Ideal.span {u}) a) *
      star (χv (Ideal.Quotient.mk (Ideal.span {v}) b)) else 0) = 0
  by_cases hx : χu (Ideal.Quotient.mk (Ideal.span {u}) a) = 0
  · simp only [hx, zero_mul, ite_self]
  by_cases hy : χv (Ideal.Quotient.mk (Ideal.span {v}) b) = 0
  · simp only [hy, star_zero, mul_zero, ite_self]
  split_ifs with h
  · exfalso
    have hd := (scaledResidue_congruence u v a b 0).mp h
    rw [sub_zero] at hd
    obtain ⟨huv, hvu⟩ := zero_frequency_units_force_divides
      (χu.apply_ne_zero_iff.mp hx) (χv.apply_ne_zero_iff.mp hy) hd
    apply hne
    apply le_antisymm
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr hvu
    · apply Ideal.span_le.mpr
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      exact Ideal.mem_span_singleton.mpr huv
  · rfl
end OAI.SevenEighths.CenteredMomentCorrelation
