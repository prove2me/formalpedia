-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:43.847753+00:00
-- url     : https://prove2.me/submissions/ab8398e1-263e-4f08-bb3a-c562a8331a8f

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
theorem _root_.solution {χ : MulChar R ℂ} {I : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (n : ℕ) : FactorsThroughIdeal (χ ^ n) I := by
  rw [factorsThroughIdeal_iff] at hχ ⊢
  intro u hu
  rw [MulChar.pow_apply_coe, hχ u hu, one_pow]
end FactorsThroughIdeal
end OAI.SevenEighths.FiniteConductor
