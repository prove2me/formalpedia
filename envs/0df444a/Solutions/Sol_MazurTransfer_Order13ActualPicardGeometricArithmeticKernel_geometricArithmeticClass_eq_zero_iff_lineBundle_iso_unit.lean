-- Prove2me | solution 1 for MazurTransfer.Order13ActualPicardGeometricArithmeticKernel.geometricArithmeticClass_eq_zero_iff_lineBundle_iso_unit
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T19:41:09.46697+00:00
-- url     : https://prove2.me/submissions/21196c00-d5ce-48aa-87f1-7c6047167a22

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the complete checked original Anthropic FLT principal-presentation
triviality argument at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a geometric field point of the same existing rational
Picard has zero arithmetic class exactly when its actual fibre line bundle
is trivial. Named downstream consumer: injectivity of the geometric class
map and promotion of diamond identities to scheme morphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricArithmeticClassDataExplicitPublicConstructors20261017
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricArithmeticClass_geometricArithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_Order13ActualPicardGeometricPointDegreeZeroPresentation_degreeZero_divisor_presentation
import Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_nonempty_iso_tensorUnit_of_principal_presentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism MazurTransfer.Order13ActualPicardGeometricDiamondLineBundle
open MazurTransfer.Order13ActualPicardGeometricArithmeticClass
open MazurTransfer.Order13GeometricRelativeCurveChange MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition MazurTransfer.LineBundleFieldComparison
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
namespace MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017
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

end MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem geometricKernelLineBundleInvertible20261017
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    Scheme.Modules.IsInvertible (actualGeometricPointLineBundle K a) :=
  geometricPointLineBundle_isInvertible (curveToBase ℚ) infinitySection actualPicard actualRepresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (geometricCurveEmbedding K) a

theorem solution
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase) :
    geometricArithmeticClass K 𝒱 a = 0 ↔
      Nonempty (actualGeometricPointLineBundle K a ≅ 𝟙_ (curveScheme K).Modules) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  constructor
  · intro ha
    obtain ⟨E, φ, hp⟩ := MazurTransfer.Order13ActualPicardGeometricPointDegreeZeroPresentation.degreeZero_divisor_presentation K 𝒱 a
    have hmk : Pic0.mk E = Pic0.mk 0 := by
      rw [Pic0.mk_zero, geometricArithmeticClass_eq_of_presentation K 𝒱 a E φ hp, ha]
    have hP : Divisor.IsPrincipal E.1 := by
      have hp0 := (MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017.pic_mk_eq_iff E.1 0).mp ((MazurTransfer.GeometricArithmeticKernelQuotientHelpers20261017.pic0_mk_eq_iff E 0).mp hmk)
      simpa only [sub_zero] using hp0
    have hχ := geometricPointLineBundle_curveEulerChar_eq (curveToBase ℚ)
      infinitySection actualPicard actualRepresentation
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (curveToBase K) (geometricCurveEmbedding K)
      (geometricCurveEmbedding_snd K) a 𝒱
    exact MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
      (curveToBase K) 𝒱 (actualGeometricPointLineBundle K a)
      (geometricKernelLineBundleInvertible20261017 K a) hχ E.1 φ hp hP
  · rintro ⟨e⟩
    obtain ⟨φ, _, hnat, hsmul, hinj, hrange⟩ :=
      Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
    have hp : IsPresentation (curveToBase K) (𝟙_ (curveScheme K).Modules) 0 φ :=
      ⟨hnat, hsmul, hinj, hrange⟩
    have hpN := hp.of_iso e
    have hz := geometricArithmeticClass_eq_of_presentation K 𝒱 a 0
      (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) hpN
    exact hz.symm.trans Pic0.mk_zero

#print axioms solution
