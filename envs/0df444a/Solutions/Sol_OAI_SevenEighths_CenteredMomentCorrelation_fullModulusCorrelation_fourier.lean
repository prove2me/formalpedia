-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullModulusCorrelation_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:02:20.050751+00:00
-- url     : https://prove2.me/submissions/2619c3b0-f5ce-4e99-89e6-75e120ea7c68

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_fourier


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (u v : A)
    [Fintype (A ⧸ Ideal.span {u})] [Fintype (A ⧸ Ideal.span {v})]
    [Fintype (A ⧸ Ideal.span {u * v})]
    (χu : MulChar (A ⧸ Ideal.span {u}) ℂ)
    (χv : MulChar (A ⧸ Ideal.span {v}) ℂ) (j : A)
    (ψ : AddChar (A ⧸ Ideal.span {u * v}) ℂ) (hψ : ψ.IsPrimitive) :
    (∑ h : A ⧸ Ideal.span {u * v},
      fourierSum ψ (scaledResidue u v (u * v) rfl) χu h *
        star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv h) *
          ψ (-(h * Ideal.Quotient.mk (Ideal.span {u * v}) j))) =
      (Fintype.card (A ⧸ Ideal.span {u * v}) : ℂ) * fullModulusCorrelation u v χu χv j :=
  fullCorrelation_fourier ψ hψ _ _ χu χv _
end OAI.SevenEighths.CenteredMomentCorrelation
