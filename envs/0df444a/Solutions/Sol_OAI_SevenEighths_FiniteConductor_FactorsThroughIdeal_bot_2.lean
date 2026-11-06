-- Prove2me | solution 2 for OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:43.263446+00:00
-- url     : https://prove2.me/submissions/9c79294c-e074-4479-911b-94142226ad23

import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CharacterTransport
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorPresentation
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorsThroughIdeal_iff


set_option autoImplicit false
open OAI
open OAI.SevenEighths
open OAI.SevenEighths.FiniteConductor
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
namespace FactorsThroughIdeal
theorem _root_.solution (χ : MulChar R ℂ) : FactorsThroughIdeal χ ⊥ := by
  rw [factorsThroughIdeal_iff]
  intro u hu
  have hu1 : (u : R) = 1 := sub_eq_zero.mp hu
  rw [hu1, map_one]
end FactorsThroughIdeal
end OAI.SevenEighths.FiniteConductor
