-- Prove2me | solution 1 for MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:15:40.288034+00:00
-- url     : https://prove2.me/submissions/83ceed08-65d7-4384-8e6c-a49216ad7b86

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: attach a genuine degree-zero divisor presentation to every
represented actual Picard point over a perfect good-characteristic field.
Named downstream consumer: arithmetic class independence and pullback naturality.
Original contract: MazurTheorem Order13ActualPicardPointDegreeZeroDivisorPresentation.
This proof compares two public Riemann-Roch identities with the public point
Euler-characteristic equality. Official Anthropic FLT presentation inputs:
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Theorems.Thm_MazurTransfer_represented_picard_field_points_classify_line_bundles
import Theorems.Thm_MazurTransfer_divisor_presentation_riemann_roch_over_perfect_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_RepresentedPicardBaseFieldPointLineBundle
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.LineBundleFieldComparison

theorem solution
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    ∃ (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens,
        Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K)),
      IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a) E.1 φ  := by
  let N := pointLineBundle (curveToBase K) ε D h a
  have hN := pointLineBundle_isInvertible (curveToBase K) ε D h a
  obtain ⟨E, φ, hnat, hsmul, hinj, hrange, _⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn (curveToBase K) N hN
  obtain ⟨_, _, _, _, hχ⟩ :=
    MazurTransfer.divisor_presentation_riemann_roch_over_perfect_field 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) N E φ hnat hsmul hinj hrange
  obtain ⟨φ₀, _, hnat₀, hsmul₀, hinj₀, hrange₀⟩ :=
    Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
  obtain ⟨_, _, _, _, hχ₀⟩ :=
    MazurTransfer.divisor_presentation_riemann_roch_over_perfect_field 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) (𝟙_ (curveScheme K).Modules) 0
      φ₀ hnat₀ hsmul₀ hinj₀ hrange₀
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  have hnχ := (MazurTransfer.represented_picard_field_points_classify_line_bundles
    (curveToBase K) ε D h).1 a |>.2 𝒱
  have hdegree : Divisor.degree E = 0 := by
    change (Module.finrank K (𝒱.sectionsOf (curveToBase K) N).H0 : ℤ) -
      Module.finrank K (𝒱.sectionsOf (curveToBase K) N).H1 = _ at hnχ
    simp only [map_zero] at hχ₀
    omega
  exact ⟨⟨E, Divisor.mem_degZero.mpr hdegree⟩, φ, ⟨hnat, hsmul, hinj, hrange⟩⟩

#print axioms solution
