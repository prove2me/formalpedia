-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/c4da153d-a996-5b7f-992c-c785259359c3

import Mathlib
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero
import Theorems.Thm_ModularCurve_DRModelPackage_range_compZero_comp_baseChangeMap_eq_closure_and_isClosed
import Theorems.Thm_ModularCurve_DRModelPackage_eq_baseChangeMap_genericPoint_of_specializes
import Theorems.Thm_ModularCurve_DRModelPackage_baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint
import Theorems.Thm_ModularCurve_DRModel_baseChangeMap_apply_notMem_preimage_basicOpen
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [IsAlgClosed (IsLocalRing.ResidueField O)]
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] (toκ : O →+* κ) :
    ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base x) =
          (DRModel.baseChangeMap (IsLocalRing.residue O)).base
            (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) := by
  intro n
  classical

  have hker : ∀ a ∈ IsLocalRing.maximalIdeal O, toκ a = 0 := by
    intro a ha
    rw [hϖ, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  let ι : IsLocalRing.ResidueField O →+* κ := Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) toκ hker
  have hι : ι.comp (IsLocalRing.residue O) = toκ := RingHom.ext fun a => rfl

  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff, hϖ]
    exact Ideal.mem_span_singleton_self _
  haveI hchar : CharP (IsLocalRing.ResidueField O) p := ringChar.eq_iff.mp (CharP.ringChar_of_prime_eq_zero Fact.out hp0)

  have hbc : DRModel.baseChangeMap (p := p) toκ =
      DRModel.baseChangeMap ι ≫ DRModel.baseChangeMap (IsLocalRing.residue O) := by
    apply pullback.hom_ext
    · simp only [DRModel.baseChangeMap, pullback.lift_fst, Category.assoc, Category.comp_id]
    · simp only [DRModel.baseChangeMap, pullback.lift_snd, Category.assoc, pullback.lift_snd_assoc, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, hι]

  have hfst : DRModel.baseChangeMap (p := p) ι ≫ pullback.fst (DRModel.toBase p) _ = pullback.fst (DRModel.toBase p) _ := by
    simp only [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]

  let x' : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))) :=
    (𝔛.compInf κ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)).base n)
  let y₀ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O))))) :=
    (DRModel.baseChangeMap ι).base x'

  have hx'inf : x' ∈ Set.range (𝔛.compInf κ).base := ⟨_, rfl⟩
  have hx'zero : x' ∈ Set.range (𝔛.compZero κ).base := by
    refine ⟨(pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)).base n, ?_⟩
    show ((pullback.snd (𝔛.compInf κ) (𝔛.compZero κ)) ≫ 𝔛.compZero κ).base n = ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ)) ≫ 𝔛.compInf κ).base n
    rw [pullback.condition]
  have hx'sm : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base x' ∉ 𝔛.smoothLocus := by
    intro h
    exact ((ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛 κ x').mp h)
      ⟨hx'inf, hx'zero⟩

  have hy₀ : y₀ ∈ Set.range (𝔛.compInf (IsLocalRing.ResidueField O)).base ∧
      y₀ ∈ Set.range (𝔛.compZero (IsLocalRing.ResidueField O)).base := by
    by_contra h
    have hmem := (ModularCurve.DRModelPackage.mem_preimage_smoothLocus_iff_not_mem_range_compInf_inter_range_compZero p 𝔛
      (IsLocalRing.ResidueField O) y₀).mpr h
    apply hx'sm
    have : (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O))))).base y₀ =
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))).base x' := by
      show (DRModel.baseChangeMap ι ≫ pullback.fst (DRModel.toBase p) _).base x' = _
      rw [hfst]
    rw [← this]
    exact hmem
  obtain ⟨a, ha⟩ := hy₀.1

  have hane : a ≠ genericPoint ↥(𝔛.ratModel (IsLocalRing.ResidueField O)).C := by
    intro hae

    have hϖ₀ : IsLocalRing.maximalIdeal (IsLocalRing.ResidueField O) = Ideal.span {((p : ℕ) : IsLocalRing.ResidueField O)} := by
      rw [hp0, Ideal.span_singleton_zero]
      exact IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField _)
    let bc₀ := DRModel.baseChangeMap (p := p) (RingHom.id (IsLocalRing.ResidueField O))
    let ξinf := (𝔛.compInf (IsLocalRing.ResidueField O) ≫ bc₀).base (genericPoint ↥(𝔛.ratModel (IsLocalRing.ResidueField O)).C)
    let ξzero := (𝔛.compZero (IsLocalRing.ResidueField O) ≫ bc₀).base (genericPoint ↥(𝔛.ratModel (IsLocalRing.ResidueField O)).C)

    have hy₀' : bc₀.base y₀ = ξinf := by
      show bc₀.base y₀ = bc₀.base ((𝔛.compInf (IsLocalRing.ResidueField O)).base (genericPoint _))
      rw [← hae, ha]
    obtain ⟨b, hb⟩ := hy₀.2
    have hmem : ξinf ∈ Set.range (𝔛.compZero (IsLocalRing.ResidueField O) ≫ bc₀).base := by
      refine ⟨b, ?_⟩
      show bc₀.base ((𝔛.compZero (IsLocalRing.ResidueField O)).base b) = ξinf
      rw [hb, hy₀']
    rw [(ModularCurve.DRModelPackage.range_compZero_comp_baseChangeMap_eq_closure_and_isClosed p 𝔛
      (IsLocalRing.ResidueField O) hϖ₀ (IsLocalRing.ResidueField O) (RingHom.id _)).1] at hmem
    have hsp : ξzero ⤳ ξinf := specializes_iff_mem_closure.mpr hmem

    have hnot := ModularCurve.DRModel.baseChangeMap_apply_notMem_preimage_basicOpen p (IsLocalRing.ResidueField O)
      (IsLocalRing.ResidueField O) (RingHom.id _) ((𝔛.compZero (IsLocalRing.ResidueField O)).base (genericPoint _))
    have heq := (ModularCurve.DRModelPackage.eq_baseChangeMap_genericPoint_of_specializes p 𝔛 (IsLocalRing.ResidueField O) hϖ₀
      (IsLocalRing.ResidueField O) (RingHom.id _)).1 ξzero hnot hsp
    exact ModularCurve.DRModelPackage.baseChangeMap_compInf_genericPoint_ne_baseChangeMap_compZero_genericPoint p 𝔛
      (IsLocalRing.ResidueField O) hϖ₀ (IsLocalRing.ResidueField O) (RingHom.id _) heq.symm

  have hacl : IsClosed ({a} : Set ↥(𝔛.ratModel (IsLocalRing.ResidueField O)).C) :=
    AlgebraicCurve.isClosed_singleton_of_ne_genericPoint (𝔛.ratModel (IsLocalRing.ResidueField O)).toBase a hane
  obtain ⟨z, hz⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton (IsLocalRing.ResidueField O)
    (𝔛.ratModel (IsLocalRing.ResidueField O)).toBase a hacl
  refine ⟨z.left ≫ 𝔛.compInf (IsLocalRing.ResidueField O), ?_, ?_⟩
  · have hco : 𝔛.compInf (IsLocalRing.ResidueField O) ≫
        pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))) =
          (𝔛.ratModel (IsLocalRing.ResidueField O)).toBase := 𝔛.compInf_over (IsLocalRing.ResidueField O)
    have hw : z.left ≫ (𝔛.ratModel (IsLocalRing.ResidueField O)).toBase = 𝟙 _ := by
      simpa only [Over.mk_left, Over.mk_hom] using Over.w z
    have e1 := congrArg (fun f => z.left ≫ f) hco
    exact (Category.assoc _ _ _).trans (e1.trans hw)
  ·
    have h1 : (DRModel.baseChangeMap ι).base x' =
        (𝔛.compInf (IsLocalRing.ResidueField O)).base (z.left.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))) := by
      rw [hz, ha]
    rw [hbc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    show (DRModel.baseChangeMap (IsLocalRing.residue O)).base ((DRModel.baseChangeMap ι).base x') = _
    rw [h1, Scheme.Hom.comp_apply]
    rfl

end S_ModularCurve_DRModelPackage_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_residueField_point_baseChangeMap_eq_of_isAlgClosed_residueField (solution)
