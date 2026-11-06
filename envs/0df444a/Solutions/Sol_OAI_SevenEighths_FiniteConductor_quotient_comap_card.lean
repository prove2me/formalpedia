-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.quotient_comap_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:42:59.386193+00:00
-- url     : https://prove2.me/submissions/de1de175-d96b-4d88-afea-81059b22dc83

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (M : Ideal R) (I : Ideal (R ⧸ M)) :
    Nat.card (R ⧸ I.comap (Ideal.Quotient.mk M)) = Nat.card ((R ⧸ M) ⧸ I) :=
  Nat.card_congr (quotientComapEquiv M I).toEquiv
end OAI.SevenEighths.FiniteConductor
