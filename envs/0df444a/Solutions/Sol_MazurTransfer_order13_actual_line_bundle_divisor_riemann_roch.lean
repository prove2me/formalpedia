-- Prove2me | solution 1 for MazurTransfer.order13_actual_line_bundle_divisor_riemann_roch
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T14:15:56.401268+00:00
-- url     : https://prove2.me/submissions/cf71c0e0-f3ac-40d1-a24d-83b1e5d87381

/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: every actual invertible sheaf on the literal order-13 curve
has a function-field divisor presentation whose cohomology satisfies the
genus-two Riemann-Roch formula over the perfect base field. Named downstream
consumer: the degree-zero arithmetic divisor class attached to an actual
Picard point over F₃ and F₅. Curve, rational place and genus: MazurTheorem WIP
at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Presentation and cohomology
arguments: official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0. ConstantsAreBase and genus two are proved actual-curve inputs.
-/
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_riemannRoch_of_constantsAreBase
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel

theorem solution
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (M : (curveScheme K).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (D : Divisor K (actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens, Γ(M, U) →+ (actualCurveFunctionField K)),
      (∀ (U V : (curveScheme K).Opens) (h : V ≤ U), Nonempty V →
        ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : (curveScheme K).Opens) [Nonempty U]
        (a : Γ(curveScheme K, U)) (m : Γ(M, U)),
        φ U (a • m) = algebraMap Γ(curveScheme K, U) (actualCurveFunctionField K) a * φ U m) ∧
      (∀ U : (curveScheme K).Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : (curveScheme K).Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf (curveToBase K) U) D : Set (actualCurveFunctionField K))) ∧
      Module.Finite K (𝒱.sectionsOf (curveToBase K) M).H0 ∧
      Module.Finite K (𝒱.sectionsOf (curveToBase K) M).H1 ∧
      Module.finrank K (𝒱.sectionsOf (curveToBase K) M).H0 = ell D ∧
      (Module.finrank K (𝒱.sectionsOf (curveToBase K) M).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf (curveToBase K) M).H1 = Divisor.degree D - 1 := by
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, _⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn (curveToBase K) M hM
  obtain ⟨h0, h1, hdim, _, hχ⟩ :=
    MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) M D φ hnat hsmul hinj hrange
  refine ⟨D, φ, hnat, hsmul, hinj, hrange, h0, h1, hdim, ?_⟩
  have hgenus := actual_genusFF_eq_two_good_characteristic K
  rw [hgenus] at hχ
  omega

#print axioms solution
