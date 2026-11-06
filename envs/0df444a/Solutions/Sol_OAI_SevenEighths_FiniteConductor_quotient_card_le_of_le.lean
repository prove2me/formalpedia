-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.quotient_card_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:13:19.560005+00:00
-- url     : https://prove2.me/submissions/029c45cb-c43d-4713-8937-cdce069fdc06

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
theorem _root_.solution {I J : Ideal R} [Finite (R ⧸ J)] (hJI : J ≤ I) :
    Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) :=
  Nat.card_le_card_of_surjective _ (Ideal.Quotient.factor_surjective hJI)
end OAI.SevenEighths.FiniteConductor
