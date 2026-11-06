-- Prove2me | solution 1 for OAI.SevenEighths.FiniteConductor.factorsThroughIdeal_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:43:46.601198+00:00
-- url     : https://prove2.me/submissions/f551f082-f313-4c75-a716-635d82aeebae

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_exists_character_factor_iff
import Theorems.Thm_OAI_SevenEighths_FiniteConductor_quotientUnits_eq_one_iff

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]
namespace OAI.SevenEighths.FiniteConductor
theorem _root_.solution (χ : MulChar R ℂ) (I : Ideal R) :
    FactorsThroughIdeal χ I ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ I → χ (u : R) = 1 := by
  let : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
  have hfactor : FactorsThroughIdeal χ I ↔
      ∃ φ : (R ⧸ I)ˣ →* ℂˣ, φ.comp (quotientUnits I) = χ.toUnitHom := by
    constructor
    · rintro ⟨φ, hφ⟩
      exact ⟨φ.toUnitHom, hφ⟩
    · rintro ⟨φ, hφ⟩
      refine ⟨MulChar.ofUnitHom φ, ?_⟩
      simpa only [MulChar.toUnitHom_eq, MulChar.ofUnitHom_eq,
        Equiv.apply_symm_apply] using hφ
  rw [hfactor, exists_character_factor_iff]
  constructor
  · intro h u hu
    have hunit := h ((quotientUnits_eq_one_iff I u).mpr hu)
    exact congrArg Units.val hunit
  · intro h u hu
    apply Units.ext
    exact h u ((quotientUnits_eq_one_iff I u).mp hu)
end OAI.SevenEighths.FiniteConductor
