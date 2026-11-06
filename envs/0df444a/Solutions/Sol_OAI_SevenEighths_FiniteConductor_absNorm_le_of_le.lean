-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.absNorm_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:02.637434+00:00
-- url     : https://prove2.me/submissions/1554b981-ac61-4d87-bada-b5037b2236e1

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotient_card_le_of_le

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution {I J : Ideal A} [Finite (A ⧸ J)] (hJI : J ≤ I) :
    I.cardQuot ≤ J.cardQuot := by
  simpa only [Submodule.cardQuot_apply] using
    quotient_card_le_of_le hJI
end OAI.SevenEighths.FiniteConductor
