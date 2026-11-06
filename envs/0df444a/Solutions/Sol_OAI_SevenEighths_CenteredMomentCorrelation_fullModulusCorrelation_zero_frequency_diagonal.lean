-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullModulusCorrelation_zero_frequency_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:29.788355+00:00
-- url     : https://prove2.me/submissions/9fafb804-fd8a-4565-b1c7-05807da192fe

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_injective
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
variable [IsDomain A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (u : A) (hu : u ≠ 0)
    [Fintype (A ⧸ Ideal.span {u})] (χ : MulChar (A ⧸ Ideal.span {u}) ℂ) :
    fullModulusCorrelation u u χ χ 0 =
      (Fintype.card (A ⧸ Ideal.span {u})ˣ : ℂ) := by
  classical
  have hinj := scaledResidue_injective u u (u * u) rfl hu
  unfold fullModulusCorrelation fullCorrelation
  have hcond (x y : A ⧸ Ideal.span {u}) :
      scaledResidue u u (u * u) rfl x -
        scaledResidue u u (u * u) (mul_comm u u) y =
        Ideal.Quotient.mk (Ideal.span {u * u}) 0 ↔ y = x := by
    rw [map_zero, sub_eq_zero]
    exact hinj.eq_iff.trans eq_comm
  simp only [hcond, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.sum_one_eq_card_units
end OAI.SevenEighths.CenteredMomentCorrelation
