-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:23.981401+00:00
-- url     : https://prove2.me/submissions/bd1455ae-b86f-47d0-aa1e-f7cce260c81c

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
variable [IsDomain A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution (d a m : A) (hm : m = d * a) (ha : a ≠ 0) :
    Function.Injective (scaledResidue d a m hm) := by
  intro x y
  refine Quotient.inductionOn₂' x y ?_
  intro r s hrs
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_singleton.mpr
  have hd := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp hrs)
  change m ∣ a * r - a * s at hd
  rw [hm, ← mul_sub, mul_comm d a] at hd
  exact (mul_dvd_mul_iff_left ha).mp hd
end OAI.SevenEighths.CenteredMomentCorrelation
