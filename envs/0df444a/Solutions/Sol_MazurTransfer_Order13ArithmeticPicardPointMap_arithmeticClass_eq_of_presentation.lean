-- Prove2me | solution 1 for MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClass_eq_of_presentation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T15:28:22.916087+00:00
-- url     : https://prove2.me/submissions/677641d2-dc3b-4cd4-a856-6a505f69e410

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full presentation-independence contract and proof retained, using
public point constructors and the accepted perfect-field presentation ratio.
Design boundary: every genuine degree-zero presentation yields the same
original arithmetic Pic0 class. Named downstream consumer: actual inverse
Picard pullback naturality. Official Anthropic FLT interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardPointMapData
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.LineBundleFieldComparison
open MazurTransfer.Order13ArithmeticPicardPointMap

namespace MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017
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

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)

noncomputable def pointPresentation :
    ∀ U : (curveScheme K).Opens,
      Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K) :=
  (MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a).choose_spec.choose

theorem pointPresentation_spec :
    IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a)
      (pointDivisor K 𝒱 ε D h a).1 (pointPresentation K 𝒱 ε D h a) :=
  (MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a).choose_spec.choose_spec

end MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017

theorem solution
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)
    (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens,
      Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K))
    (hE : IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a) E.1 φ) :
    Pic0.mk E = arithmeticClass K 𝒱 ε D h a := by
  let N := pointLineBundle (curveToBase K) ε D h a
  have hp := MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017.pointPresentation_spec K 𝒱 ε D h a
  have hsec : ∃ (U : (curveScheme K).Opens) (m : Γ(N, U)), m ≠ 0 := by
    obtain ⟨U, s, hη, hs⟩ :=
      (pointLineBundle_isInvertible (curveToBase K) ε D h a).exists_isFrameOn
        (genericPoint (curveScheme K))
    letI : Nonempty U := ⟨⟨_, hη⟩⟩
    exact ⟨U, s,
      MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017.frame_ne_zero hs⟩
  obtain ⟨_, _, _, _, hP⟩ :=
    MazurTransfer.presentation_ratio_principal_over_perfect_field
      (curveToBase K) (actual_constantsAreBase_good_characteristic K) N E.1
      (pointDivisor K 𝒱 ε D h a).1 φ (MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017.pointPresentation K 𝒱 ε D h a)
      hE.nat hp.nat hE.smul hp.smul hE.inj hp.inj hE.range hp.range hsec
  exact (MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017.pic0_mk_eq_iff E (pointDivisor K 𝒱 ε D h a)).mpr
    ((MazurTransfer.Order13ArithmeticPicardPresentationIndependenceHelpers20261017.pic_mk_eq_iff _ _).mpr hP)


#print axioms solution
