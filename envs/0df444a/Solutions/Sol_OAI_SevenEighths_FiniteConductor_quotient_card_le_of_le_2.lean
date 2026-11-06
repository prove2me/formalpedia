-- Prove2me | solution 2 for OAI.SevenEighths.FiniteConductor.quotient_card_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:30.56125+00:00
-- url     : https://prove2.me/submissions/2a7c3fc5-603e-438a-8fa1-02b2c5c365fb

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

theorem solution {I J : Ideal R} [Finite (R ⧸ J)] (hJI : J ≤ I) :
    Nat.card (R ⧸ I) ≤ Nat.card (R ⧸ J) :=
  Nat.card_le_card_of_surjective _ (Ideal.Quotient.factor_surjective hJI)
