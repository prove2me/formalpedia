-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.dvd_of_unit_residue_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:05.89004+00:00
-- url     : https://prove2.me/submissions/9d866205-6cc4-4819-8230-fe0357566769

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
theorem _root_.solution {u x v : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x)) (hdiv : u ∣ v * x) : u ∣ v := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hm : Ideal.Quotient.mk (Ideal.span {u}) v *
      Ideal.Quotient.mk (Ideal.span {u}) x = 0 := by
    rw [← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
  exact hx.mul_right_injective (by simpa only [mul_comm, mul_zero, zero_mul] using hm)
end OAI.SevenEighths.CenteredMomentCorrelation
