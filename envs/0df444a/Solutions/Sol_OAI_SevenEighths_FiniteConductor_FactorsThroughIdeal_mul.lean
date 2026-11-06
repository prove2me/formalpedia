-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.FactorsThroughIdeal.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:40.241138+00:00
-- url     : https://prove2.me/submissions/cc3f9a67-7471-411c-9f32-3402b4953ea4

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_factorsThroughIdeal_iff


set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
namespace FactorsThroughIdeal
theorem _root_.solution {χ ψ : MulChar R ℂ} {I J : Ideal R}
    (hχ : FactorsThroughIdeal χ I) (hψ : FactorsThroughIdeal ψ J) :
    FactorsThroughIdeal (χ * ψ) (I ⊓ J) := by
  rw [factorsThroughIdeal_iff] at hχ hψ ⊢
  intro u hu
  rw [MulChar.mul_apply, hχ u hu.1, hψ u hu.2, one_mul]
end FactorsThroughIdeal
end OAI.SevenEighths.FiniteConductor
