-- Prove2me | solution 1 for OAI.SevenEighths.ConductorPresentation.source_le_comap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:02.249819+00:00
-- url     : https://prove2.me/submissions/8a086698-dd82-4495-83e8-fc6f6f1a77d1

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
namespace OAI.SevenEighths.ConductorPresentation
theorem _root_.solution (M : Ideal A) (I : Ideal (A ⧸ M)) :
    M ≤ I.comap (Ideal.Quotient.mk M) := by
  intro a ha
  change Ideal.Quotient.mk M a ∈ I
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
  exact I.zero_mem
end OAI.SevenEighths.ConductorPresentation
