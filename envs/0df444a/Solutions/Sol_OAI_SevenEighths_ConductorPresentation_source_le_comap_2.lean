-- Prove2me | solution 2 for OAI.SevenEighths.ConductorPresentation.source_le_comap
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:33.655011+00:00
-- url     : https://prove2.me/submissions/56f28a2c-8060-4b32-aa30-092a17f6c1b9

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.ConductorPresentation
open SevenEighths.FiniteFourier SevenEighths.FiniteConductor
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A]
theorem solution (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro x hx
  show Ideal.Quotient.mk M x ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  exact I.zero_mem
