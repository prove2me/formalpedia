-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_congruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:41:27.979026+00:00
-- url     : https://prove2.me/submissions/3b311830-d2f8-4b0d-818e-30b12ab4500a

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (u v x y j : A) :
    scaledResidue u v (u * v) rfl (Ideal.Quotient.mk (Ideal.span {u}) x) -
      scaledResidue v u (u * v) (mul_comm u v)
        (Ideal.Quotient.mk (Ideal.span {v}) y) =
      Ideal.Quotient.mk (Ideal.span {u * v}) j ↔
      u * v ∣ v * x - u * y - j := by
  rw [scaledResidue_mk, scaledResidue_mk, ← map_sub, Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton
end OAI.SevenEighths.CenteredMomentCorrelation
