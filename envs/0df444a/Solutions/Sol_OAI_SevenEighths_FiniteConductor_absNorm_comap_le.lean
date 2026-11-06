-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.absNorm_comap_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:26.488601+00:00
-- url     : https://prove2.me/submissions/a48172c9-1eb5-4eed-806f-c3234b672434

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_le_of_le

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (M : Ideal A) [Finite (A ⧸ M)] (I : Ideal (A ⧸ M)) :
    (I.comap (Ideal.Quotient.mk M)).cardQuot ≤ M.cardQuot := by
  apply absNorm_le_of_le
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem
end OAI.SevenEighths.FiniteConductor
