-- Prove2me | solution 1 for MazurTransfer.PublicArithmeticPicardGroupEquiv.arithmeticClassOver_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-18T17:44:53.205507+00:00
-- url     : https://prove2.me/submissions/98af54d6-142a-4247-984c-eadd179b3660

import Mathlib
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardOverHomPointMapsOriginalData20261018
import Definitions.Def_MazurTransfer_Order13PublicFunctionFieldInvariants
import Definitions.Def_MazurTransfer_OriginalDivisorPresentationTransportDataExplicitSectionSpaces20261017
import Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
import Theorems.Thm_MazurTransfer_order13_actual_function_field_invariants
import Theorems.Thm_MazurTransfer_all_divisor_classes_realized_over_perfect_field
import Theorems.Thm_MazurTransfer_FieldDivisorComparison_riemannRoch_of_constantsAreBase
import Theorems.Thm_MazurTransfer_order13_actual_tensorUnit_curveEulerChar
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
import Theorems.Thm_MazurTransfer_represented_picard_field_points_classify_line_bundles
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses original official Anthropic FLT Picard, divisor presentation and cohomology interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the original arithmetic Picard class map on Over-category points is surjective over every perfect field with 104 nonzero. Arbitrary closed points are included by the accepted full divisor-realization theorem. Named downstream consumer: the original rational Picard class-group equivalence and actual rational norm-kernel comparison.
-/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.LineBundleFieldComparison MazurTransfer.Order13ArithmeticPicardPointMap
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
namespace MazurTransfer.ArithmeticPicardOverHomSurjectivityProofHelpers20261018
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
end MazurTransfer.ArithmeticPicardOverHomSurjectivityProofHelpers20261018

theorem solution (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D) :
    Function.Surjective (arithmeticClassOver K 𝒱 ε D h) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  letI : IsCurveOver K (actualCurveFunctionField K) :=
    (MazurTransfer.order13_actual_function_field_invariants K Fact.out).1
  intro c
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective c
  obtain ⟨M, hM, G, φ, hnat, hsmul, hinj, hrange, hP⟩ :=
    MazurTransfer.all_divisor_classes_realized_over_perfect_field
      (curveToBase K) (actual_constantsAreBase_good_characteristic K) E.1
  have hp : IsPresentation (curveToBase K) M G φ := ⟨hnat, hsmul, hinj, hrange⟩
  have hdegree : Divisor.degree G = 0 := by
    have hz : Divisor.degree (G - E.1) = 0 := by
      obtain ⟨f, hf, hfval⟩ := hP
      obtain ⟨D₀, hD₀, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
      have heq : G - E.1 = D₀ := Finsupp.ext fun v => (hfval v).trans (hD₀ v).symm
      rw [heq, hdeg]
    rw [map_sub] at hz
    have he := Divisor.mem_degZero.mp E.2
    omega
  obtain ⟨_, _, _, _, hχ⟩ :=
    MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) M G φ hp.nat hp.smul hp.inj hp.range
  rw [actual_genusFF_eq_two_good_characteristic K, hdegree] at hχ
  have hχM : curveEulerChar (curveToBase K) 𝒱 M =
      curveEulerChar (curveToBase K) 𝒱 (𝟙_ (curveScheme K).Modules) := by
    rw [MazurTransfer.order13_actual_tensorUnit_curveEulerChar K 𝒱]
    change curveEulerChar (curveToBase K) 𝒱 M = _ at hχ
    omega
  obtain ⟨a, ⟨e⟩, _⟩ :=
    (MazurTransfer.represented_picard_field_points_classify_line_bundles
      (curveToBase K) ε D h).2.2 𝒱 M hM hχM
  let G0 : Divisor.degZero (K := K) (F := actualCurveFunctionField K) :=
    ⟨G, Divisor.mem_degZero.mpr hdegree⟩
  have ha := arithmeticClass_eq_of_presentation K 𝒱 ε D h a G0
    (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) (hp.of_iso e)
  have hm : Pic0.mk G0 = Pic0.mk E :=
    (MazurTransfer.ArithmeticPicardOverHomSurjectivityProofHelpers20261018.pic0_mk_eq_iff G0 E).mpr
      ((MazurTransfer.ArithmeticPicardOverHomSurjectivityProofHelpers20261018.pic_mk_eq_iff G E.1).mpr hP)
  exact ⟨overHomOfPoint K D a, ha.symm.trans hm⟩
#print axioms solution
#print axioms MazurTransfer.ArithmeticPicardOverHomSurjectivityProofHelpers20261018.pic_mk_eq_iff
#print axioms MazurTransfer.ArithmeticPicardOverHomSurjectivityProofHelpers20261018.pic0_mk_eq_iff
