-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.bot
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:00.321983+00:00
-- url     : https://prove2.me/submissions/a15ea3b9-e3c1-482d-a342-7acc23d12279

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.FiniteConductor
variable {R : Type*} [CommRing R] [Finite R]

theorem solution (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  refine ⟨CharacterTransport.pullback (RingEquiv.quotientBot R) χ, ?_⟩
  ext u
  simp [quotientUnits, CharacterTransport.pullback, RingEquiv.quotientBot_mk]
