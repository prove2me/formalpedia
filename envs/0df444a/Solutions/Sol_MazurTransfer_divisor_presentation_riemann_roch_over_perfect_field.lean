-- Prove2me | solution 1 for MazurTransfer.divisor_presentation_riemann_roch_over_perfect_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T23:23:37.682935+00:00
-- url     : https://prove2.me/submissions/47dbe457-6733-4385-a98c-481baf868da2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: full cohomological Riemann–Roch for actual divisor
presentations over perfect fields with the full constant field explicit.
Named downstream consumer: the unchanged actual order-13 arithmetic
Picard group correspondence. The original public theorem is unchanged.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import Mathlib.Tactic.Linarith

open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace
universe u
namespace MazurTransfer.PublicPresentationRiemannRochHelpers
theorem ne_top_of_isAffineOpen_e9' {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

end MazurTransfer.PublicPresentationRiemannRochHelpers
open MazurTransfer.PublicPresentationRiemannRochHelpers

theorem solution
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)) :
    letI := (baseToFunctionField x).toAlgebra
    Module.Finite K (𝒱.sectionsOf x M).H0 ∧ Module.Finite K (𝒱.sectionsOf x M).H1 ∧
      Module.finrank K (𝒱.sectionsOf x M).H0 = ell D ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = indexOfSpecialty D ∧
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1
        = Divisor.degree D + 1 - genusFF K X.functionField := by
  letI := (baseToFunctionField x).toAlgebra
  haveI hcurve : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one x (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField x
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen_e9' hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen_e9' hNA 𝒱.isAffineOpen_U1
  have h0 : Nonempty 𝒱.U0 := by
    by_contra hc
    apply hne1
    have hb : 𝒱.U0 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, bot_sup_eq] at this
  have h1 : Nonempty 𝒱.U1 := by
    by_contra hc
    apply hne0
    have hb : 𝒱.U1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, sup_bot_eq] at this
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top x 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨v₀, hv₀⟩ := hS0
  haveI : Nonempty (Place K X.functionField) := ⟨v₀⟩
  obtain ⟨-, hL0, γ, D₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI := hL0

  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ :=
    nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn 𝒱 x h0 h1 M D φ hnat
      (fun U _ a m => hsmul U a m) hinj hrange
  obtain ⟨hfin0, hfin1, hrk0, hrk1, hchi, -⟩ := cechRiemannRoch_of_genusReached hγ hcov ⟨v₀, hv₀⟩ hS1 D

  have hγg : (genusFF K X.functionField : ℤ) = γ := by
    have h0 := (indexOfSpecialty_eq_of_genusReached hγ (0 : Divisor K X.functionField)).2
    rw [ell_zero_eq_one_of_constantsAreBase hC, map_zero, indexOfSpecialty_eq_finrank_H1] at h0
    change (Module.finrank K (H1 (0 : Divisor K X.functionField)) : ℤ) = γ
    simp only [Nat.cast_one, zero_add] at h0
    linarith only [h0]
  haveI : Module.Finite K ↥(cechH0 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) := hfin0
  haveI : Module.Finite K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) := hfin1
  refine ⟨Module.Finite.equiv e0.symm, Module.Finite.equiv e1.symm, ?_, ?_, ?_⟩
  · rw [e0.finrank_eq, hrk0]
  · rw [e1.finrank_eq, hrk1]
  · rw [e0.finrank_eq, e1.finrank_eq, hγg]
    exact hchi

#print axioms solution
