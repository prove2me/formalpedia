-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:05:56.954869+00:00
-- url     : https://prove2.me/submissions/4595bcce-f926-4239-8059-97205f8c7f20

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every perfect characteristic-zero field point of the same
existing rational represented Picard has a full degree-zero divisor
presentation on the literal curve over that field. Named downstream
consumer: the geometric arithmetic class of the rational Picard diamond.
-/
import Theorems.Thm_MazurTransfer_divisor_presentation_riemann_roch_over_perfect_field
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13GeometricRelativeCurveChange
open MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition MazurTransfer.LineBundleFieldComparison
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance geometricPresentationFactK : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance geometricPresentationFactQ : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance geometricPresentationAlgebraK : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
theorem actualGeometricPointLineBundleIsInvertibleForPublicPresentation20261017
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Scheme.Modules.IsInvertible (actualGeometricPointLineBundle K a) :=
  geometricPointLineBundle_isInvertible (curveToBase ℚ) infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K) a

theorem solution
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    ∃ (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens,
        Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K),
      IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a) E.1 φ := by
  let N := actualGeometricPointLineBundle K a
  have hN := actualGeometricPointLineBundleIsInvertibleForPublicPresentation20261017 K a
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
  have hnχ := geometricPointLineBundle_curveEulerChar_eq (curveToBase ℚ)
    infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (curveToBase K) (geometricCurveEmbedding K)
    (geometricCurveEmbedding_snd K) a 𝒱
  have hdegree : Divisor.degree E = 0 := by
    change (Module.finrank K (𝒱.sectionsOf (curveToBase K) N).H0 : ℤ) -
      Module.finrank K (𝒱.sectionsOf (curveToBase K) N).H1 = _ at hnχ
    unfold curveEulerChar at hnχ
    simp only [map_zero] at hχ₀
    omega
  exact ⟨⟨E, Divisor.mem_degZero.mpr hdegree⟩, φ, ⟨hnat, hsmul, hinj, hrange⟩⟩

#print axioms solution
