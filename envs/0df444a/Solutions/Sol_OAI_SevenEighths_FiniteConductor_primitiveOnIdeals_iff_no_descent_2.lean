-- Prove2me | solution 2 for OAI.SevenEighths.FiniteConductor.primitiveOnIdeals_iff_no_descent
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:48:46.604333+00:00
-- url     : https://prove2.me/submissions/388774a8-4eb4-4955-b27c-ccbea10e6fa4

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteFourier
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Order.Preorder.Finite
import Mathlib.RingTheory.Ideal.Maps
import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [Finite R]

theorem OA2Aux.factorsThroughIdeal_iff (χ : MulChar R ℂ) (I : Ideal R) :
    FactorsThroughIdeal χ I ↔
      ∀ u : Rˣ, (u : R) - 1 ∈ I → χ (u : R) = 1 := by
  constructor
  · rintro ⟨φ, hφ⟩ u hu
    have h1 : quotientUnits I u = 1 := by
      apply Units.ext
      show Ideal.Quotient.mk I (u : R) = 1
      rw [← map_one (Ideal.Quotient.mk I)]
      exact Ideal.Quotient.eq.mpr hu
    have h2 : φ.toUnitHom (quotientUnits I u) = χ.toUnitHom u := DFunLike.congr_fun hφ u
    rw [h1, map_one] at h2
    have h3 := congrArg Units.val h2
    rw [MulChar.coe_toUnitHom] at h3
    simpa using h3.symm
  · intro h
    have hker : (quotientUnits I).ker ≤ χ.toUnitHom.ker := by
      intro u hu
      rw [MonoidHom.mem_ker] at hu ⊢
      apply Units.ext
      rw [MulChar.coe_toUnitHom]
      apply h
      have h1 : Ideal.Quotient.mk I (u : R) = 1 := congrArg Units.val hu
      rw [← map_one (Ideal.Quotient.mk I)] at h1
      exact Ideal.Quotient.eq.mp h1
    let H : Subgroup (R ⧸ I)ˣ := (quotientUnits I).range
    let f : Rˣ →* H := (quotientUnits I).rangeRestrict
    have hf : Function.Surjective f := (quotientUnits I).rangeRestrict_surjective
    have hkerf : f.ker ≤ χ.toUnitHom.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    let g : H →* ℂˣ := f.liftOfSurjective hf ⟨χ.toUnitHom, hkerf⟩
    haveI : Finite (R ⧸ I) := Finite.of_surjective _ (Ideal.Quotient.mk_surjective (I := I))
    haveI : Finite (R ⧸ I)ˣ := Finite.of_injective Units.val Units.val_injective
    obtain ⟨φ', hφ'⟩ := (MonoidHom.domRestrict_surjective ℂ H) g
    refine ⟨MulChar.ofUnitHom φ', ?_⟩
    ext u
    have e1 : φ' (quotientUnits I u) = g (f u) := by
      rw [← hφ']
      rfl
    have e2 : g (f u) = χ.toUnitHom u :=
      MonoidHom.liftOfRightInverse_comp_apply f _ _ ⟨χ.toUnitHom, hkerf⟩ u
    show ((MulChar.ofUnitHom φ').toUnitHom (quotientUnits I u) : ℂ) = (χ.toUnitHom u : ℂ)
    rw [MulChar.coe_toUnitHom]
    show (MulChar.ofUnitHom φ') ((quotientUnits I u : (R ⧸ I)ˣ) : R ⧸ I) = _
    rw [MulChar.ofUnitHom_coe, e1, e2]

theorem solution (χ : MulChar R ℂ) :
    IsPrimitiveOnIdeals χ ↔ ∀ I : Ideal R, I ≠ ⊥ → ¬ FactorsThroughIdeal χ I := by
  unfold IsPrimitiveOnIdeals
  constructor
  · intro h I hI hf
    obtain ⟨u, hu1, hu2⟩ := h I hI
    exact hu2 ((OA2Aux.factorsThroughIdeal_iff χ I).mp hf u hu1)
  · intro h I hI
    by_contra hcon
    apply h I hI
    rw [OA2Aux.factorsThroughIdeal_iff]
    intro u hu
    by_contra hne
    exact hcon ⟨u, hu, hne⟩
