-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.zero_frequency_units_force_divides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:28:46.978192+00:00
-- url     : https://prove2.me/submissions/e02ea8a9-5827-4a79-9550-1f836661c70d

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_scaledResidue_mk
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_dvd_of_unit_residue_mul
attribute [local simp] OAI.SevenEighths.CenteredMomentCorrelation.scaledResidue_mk

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
variable {A : Type*} [CommRing A]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution {u v x y : A}
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {u}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {v}) y))
    (hcong : u * v ∣ v * x - u * y) : u ∣ v ∧ v ∣ u := by
  have hu : u ∣ v * x := by
    have h := dvd_add ((dvd_mul_right u v).trans hcong) (dvd_mul_right u y)
    simpa only [sub_add_cancel] using h
  have hv : v ∣ u * y := by
    have h := dvd_sub (dvd_mul_right v x) ((dvd_mul_left v u).trans hcong)
    convert h using 1 ; ring
  exact ⟨dvd_of_unit_residue_mul hx hu, dvd_of_unit_residue_mul hy hv⟩
end OAI.SevenEighths.CenteredMomentCorrelation
