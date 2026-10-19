-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricArithmeticClass.geometricArithmeticClass_eq_of_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:24:22.342986+00:00
-- url     : https://prove2.me/submissions/9669a481-e02a-4900-9978-500d1e802a32

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the same existing rational represented Picard has an
intrinsic degree-zero divisor class at every perfect characteristic-zero
field point. The existing rational diamond transports this class by the
actual extension-field diamond. Named downstream consumer: promoting the
arithmetic diamond cyclotomic relation to a scheme morphism identity.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGenericFieldAction
open MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle MazurTransfer.Order13ActualPicardGeometricDiamondPresentation
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
namespace MazurTransfer.GeometricArithmeticPicardPresentationIndependenceHelpers20261017
section QuotientComparison
variable {K : Type u} [Field K] {F : Type u} [Field F] [Algebra K F]
theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]
theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F) = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]
end QuotientComparison

theorem frame_ne_zero {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : Scheme.Modules.IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

end MazurTransfer.GeometricArithmeticPicardPresentationIndependenceHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase)

noncomputable def geometricChosenPresentation20261017 : ∀ U : (curveScheme K).Opens,
    Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K :=
  (MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a).choose_spec.choose

theorem geometricChosenPresentationSpec20261017 :
    IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a)
      (geometricPointDivisor K 𝒱 a).1 (geometricChosenPresentation20261017 K 𝒱 a) :=
  (MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a).choose_spec.choose_spec

theorem solution
    (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens,
      Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K)
    (hE : IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a) E.1 φ) :
    Pic0.mk E = geometricArithmeticClass K 𝒱 a := by
  let N := actualGeometricPointLineBundle K a
  have hp := geometricChosenPresentationSpec20261017 K 𝒱 a
  have hsec : ∃ (U : (curveScheme K).Opens) (m : Γ(N, U)), m ≠ 0 := by
    obtain ⟨U, s, hη, hs⟩ :=
      (MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition.geometricPointLineBundle_isInvertible (curveToBase ℚ) infinitySection actualPicard actualRepresentation (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (MazurTransfer.Order13GeometricRelativeCurveChange.geometricCurveEmbedding K) a).exists_isFrameOn
        (genericPoint (curveScheme K))
    letI : Nonempty U := ⟨⟨_, hη⟩⟩
    exact ⟨U, s,
      MazurTransfer.GeometricArithmeticPicardPresentationIndependenceHelpers20261017.frame_ne_zero hs⟩
  obtain ⟨_, _, _, _, hP⟩ :=
    MazurTransfer.presentation_ratio_principal_over_perfect_field
      (curveToBase K) (actual_constantsAreBase_good_characteristic K) N E.1
      (geometricPointDivisor K 𝒱 a).1 φ (geometricChosenPresentation20261017 K 𝒱 a)
      hE.nat hp.nat hE.smul hp.smul hE.inj hp.inj hE.range hp.range hsec
  exact (MazurTransfer.GeometricArithmeticPicardPresentationIndependenceHelpers20261017.pic0_mk_eq_iff E (geometricPointDivisor K 𝒱 a)).mpr
    ((MazurTransfer.GeometricArithmeticPicardPresentationIndependenceHelpers20261017.pic_mk_eq_iff _ _).mpr hP)


#print axioms solution
