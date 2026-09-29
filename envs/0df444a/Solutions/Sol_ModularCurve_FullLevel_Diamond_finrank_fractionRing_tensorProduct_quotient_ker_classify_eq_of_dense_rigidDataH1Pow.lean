-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/25c69aa0-6005-5083-8f87-65f7416f8c98

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_XH
import Theorems.Thm_ModularCurve_FullLevel_Diamond_isIntegral_adjoin_j0_levelModuliPackageAbs_rigidDataH1Pow
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree
import Theorems.Thm_ModularCurve_FullLevel_Diamond_two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
import Theorems.Thm_ModularCurve_dedekindPsi_eq_prod_primeFactors
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.Generic.isElliptic_curve WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄ WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq"
p2m_attr_erase "simp" "NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups TensorProduct

theorem degreeH1_aux
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) [Fact ℓg.Prime] (hℓg3 : 3 ≤ ℓg) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M')
        (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)))
    (y : ↥K) (hy : ((y : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q) :
    Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        (ℓg - 1) * (q * (q ^ 2 - 1)) / 2 := by
  have hqp : q.Prime := Fact.out
  have hℓp : ℓg.Prime := Fact.out
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  haveI hN0 : NeZero (q ^ 2 * M') := ⟨Nat.mul_ne_zero (pow_ne_zero 2 hqp.ne_zero) (NeZero.ne M')⟩
  subst hK

  have hjq : ModularCurve.jq ∈ ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) := by
    have h1 : ModularCurve.jqModC ℚ ∈ ModularCurve.modularFunctionFieldC ℚ (q ^ 2 * M') :=
      ModularCurve.jqModC_mem ℚ _
    rw [ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero] at h1
    exact ModularCurve.x0_le_xHFunctionFieldC ℚ _ _
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ _ h1)
  have hxmem : ModularCurve.jqModC L ∈ (ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))) := by
    rw [← ModularCurve.coeffEmb_jq]
    exact ModularCurve.coeffEmb_mem_laurentBaseChange L hjq
  let x : ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))) := ⟨ModularCurve.jqModC L, hxmem⟩

  have hB1 : Module.finrank ↥(IntermediateField.adjoin L ({x} : Set ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))))) ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))) =
      (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) ⊔
        Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).index :=
    ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index_of_algebraRat
      L (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) x rfl

  have hG3 := ModularCurve.FullLevel.Diamond.two_mul_index_gammaH_levelH_inf_ker_sup_zpowers_neg_one_eq
    q ℓg hℓg3 M' hqM' hℓgM'

  have hG4 := ModularCurve.dedekindPsi_eq_prod_primeFactors M' (NeZero.ne M')
  have hψpos : 0 < ModularCurve.dedekindPsi M' := by
    rw [hG4]
    exact Finset.prod_pos fun p hp =>
      Nat.mul_pos (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _) (Nat.succ_pos p)
  have hidxpos : 0 < (CohCarrier.GammaH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) ⊔
        Subgroup.zpowers (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ)).index := by
    have h1 : 0 < q * (q ^ 2 - 1) := Nat.mul_pos hqp.pos (Nat.sub_pos_of_lt (by nlinarith [hqp.two_le]))
    have h2 : 0 < ℓg - 1 := by omega
    have := Nat.mul_pos (Nat.mul_pos h1 h2) hψpos
    rw [← hG3] at this
    omega
  haveI : Module.Free ↥(IntermediateField.adjoin L ({x} : Set ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))))) ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))) := Module.Free.of_divisionRing _ _
  haveI : FiniteDimensional ↥(IntermediateField.adjoin L ({x} : Set ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))))) ↥(ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker))) :=
    Module.finite_of_finrank_pos (by rw [hB1]; exact hidxpos)

  have hsq : Squarefree q := hqp.prime.squarefree
  rw [ModularCurve.finrank_adjoin_jqNModC_eq_finrank_adjoin_jqModC_of_squarefree L q hsq hqp.one_lt _ x y
      rfl hy, hB1, ← hG4]
  symm
  apply Nat.div_eq_of_eq_mul_left two_pos
  linarith [hG3]

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (x : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.Pt ↥K)
    (hx : (((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf x : ↥K) : LaurentSeries L) =
      ModularCurve.jqNModC L q)
    [IsDomain ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))]
    (hdense : ∀ k : ↥K, ∃ a b : P₀.B₀, P₀.classify x b ≠ 0 ∧ k * P₀.classify x b = P₀.classify x a) :
    letI S := ↥(Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀))
    letI F := FractionRing S
    Module.finrank F (TensorProduct S F (P₀.B₀ ⧸ RingHom.ker (P₀.classify x).toRingHom)) =
      (∏ p ∈ M'.primeFactors, p ^ (M'.factorization p - 1) * (p + 1)) *
        (ℓg - 1) * (q * (q ^ 2 - 1)) / 2 := by
  classical

  set ι : P₀.B₀ →ₐ[A] ↥K := P₀.classify x with hιdef
  set 𝔭 : Ideal P₀.B₀ := RingHom.ker ι.toRingHom with h𝔭
  set S : Subalgebra A P₀.B₀ := Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀) with hSdef
  haveI : Fact ℓg.Prime := ⟨hℓg⟩
  have hℓg3 : 3 ≤ ℓg := by omega
  have hℓg5 : 5 ≤ ℓg := by omega
  subst hH₁

  have hy : ((ι P₀.j₀ : ↥K) : LaurentSeries L) = ModularCurve.jqNModC L q := by
    rw [← hx]; congr 1
    show ι ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) = _
    rw [← (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf_map ι P₀.univ, hιdef, P₀.map_classify]
  set y : ↥K := ι P₀.j₀ with hydef
  have hD2 := degreeH1_aux q M' hqM' ℓg hℓg3 hℓgM' L K hK y hy

  have hint : Algebra.IsIntegral ↥S P₀.B₀ :=
    ModularCurve.FullLevel.Diamond.isIntegral_adjoin_j0_levelModuliPackageAbs_rigidDataH1Pow
      A q ℓg M' hℓg5 hℓA hM'A hℓ hM hL 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 hVC hCO P₀
  have hιS : ∀ s : ↥S, ι (s : P₀.B₀) = 0 → s = 0 := by

    set κ : P₀.B₀ →+* LaurentSeries L := (IntermediateField.val K).toRingHom.comp ι.toRingHom with hκ
    have hκapp : ∀ b : P₀.B₀, κ b = ((ι b : ↥K) : LaurentSeries L) := fun b => rfl
    have hκA : κ.comp (algebraMap A P₀.B₀) = (algebraMap L (LaurentSeries L)).comp (algebraMap A L) := by
      ext a
      simp only [RingHom.comp_apply, hκapp, AlgHom.commutes, IsScalarTower.algebraMap_apply A L ↥K a]
      rfl
    have hκf : ∀ f : Polynomial A, κ (Polynomial.aeval P₀.j₀ f) =
        Polynomial.aeval (κ P₀.j₀) (f.map (algebraMap A L)) := by
      intro f
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, ← hκA, ← Polynomial.hom_eval₂]
    have hT : Transcendental L (κ P₀.j₀) := by
      rw [hκapp, hy]; exact ModularCurve.transcendental_jqNModC L q
    intro s hs
    have hsr : ∃ f : Polynomial A, Polynomial.aeval P₀.j₀ f = (s : P₀.B₀) := by
      have : (s : P₀.B₀) ∈ (Polynomial.aeval (R := A) P₀.j₀).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact s.2
      exact this
    obtain ⟨f, hf⟩ := hsr
    have hfκ : Polynomial.aeval (κ P₀.j₀) (f.map (algebraMap A L)) = 0 := by
      rw [← hκf, hf, hκapp, hs]; rfl
    have hf0 : f.map (algebraMap A L) = 0 := (transcendental_iff.mp hT) _ hfκ
    have hf00 : f = 0 := by rwa [Polynomial.map_eq_zero_iff (IsFractionRing.injective A L)] at hf0
    apply Subtype.ext
    show (s : P₀.B₀) = 0
    rw [← hf, hf00, map_zero]

  let ιS : ↥S →ₐ[A] ↥K := ι.comp S.val
  have hιS_inj : Function.Injective ιS := by
    intro s₁ s₂ h
    have : ι ((s₁ - s₂ : ↥S) : P₀.B₀) = 0 := by
      rw [Subalgebra.coe_sub, map_sub]; exact sub_eq_zero.mpr h
    exact sub_eq_zero.mp (hιS _ this)
  letI algSK : Algebra ↥S ↥K := ιS.toRingHom.toAlgebra
  have hSK : ∀ s : ↥S, algebraMap ↥S ↥K s = ι (s : P₀.B₀) := fun s => rfl
  haveI : IsScalarTower ↥S P₀.B₀ (P₀.B₀ ⧸ 𝔭) := IsScalarTower.of_algebraMap_eq (fun s => rfl)

  let FK : (FractionRing ↥S) →+* ↥K := IsFractionRing.lift (K := (FractionRing ↥S)) (g := algebraMap ↥S ↥K) hιS_inj
  have hFK : ∀ s : ↥S, FK (algebraMap ↥S (FractionRing ↥S) s) = ι (s : P₀.B₀) := fun s => by
    show IsFractionRing.lift _ _ = _
    rw [IsFractionRing.lift_algebraMap]; rfl
  letI algFK : Algebra (FractionRing ↥S) ↥K := FK.toAlgebra
  haveI : IsScalarTower ↥S (FractionRing ↥S) ↥K := IsScalarTower.of_algebraMap_eq (fun s => (hFK s).symm)

  let ῑ : (P₀.B₀ ⧸ 𝔭) →ₐ[↥S] ↥K :=
    { toRingHom := ι.toRingHom.kerLift
      commutes' := fun s => by
        show ι.toRingHom.kerLift (Ideal.Quotient.mk 𝔭 ((s : P₀.B₀))) = ι (s : P₀.B₀)
        exact RingHom.kerLift_mk _ _ }
  have hῑ_inj : Function.Injective ῑ := RingHom.kerLift_injective _
  have hῑ_mk : ∀ b : P₀.B₀, ῑ (Ideal.Quotient.mk 𝔭 b) = ι b := fun b => RingHom.kerLift_mk _ _

  let φ : TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭) →ₐ[(FractionRing ↥S)] ↥K :=
    Algebra.TensorProduct.lift (Algebra.ofId (FractionRing ↥S) ↥K) ῑ (fun _ _ => Commute.all _ _)
  have hφ_tmul : ∀ (f : (FractionRing ↥S)) (d : (P₀.B₀ ⧸ 𝔭)), φ (f ⊗ₜ d) = FK f * ῑ d := fun f d => by
    show Algebra.TensorProduct.lift _ _ _ (f ⊗ₜ d) = _
    rw [Algebra.TensorProduct.lift_tmul]; rfl

  have hφ_inj : Function.Injective φ := by
    letI : Algebra (P₀.B₀ ⧸ 𝔭) (TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭)) := Algebra.TensorProduct.rightAlgebra
    haveI hloc : IsLocalization (Algebra.algebraMapSubmonoid (P₀.B₀ ⧸ 𝔭) (nonZeroDivisors ↥S)) (TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭)) :=
      IsLocalization.tensorRight (R := ↥S) (S := (P₀.B₀ ⧸ 𝔭)) (A := (FractionRing ↥S)) (nonZeroDivisors ↥S)
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro z hz
    obtain ⟨⟨d, s⟩, hds⟩ := IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (P₀.B₀ ⧸ 𝔭) (nonZeroDivisors ↥S)) z
    dsimp only at hds
    rw [← hds] at hz ⊢
    have halg : ∀ d' : (P₀.B₀ ⧸ 𝔭), algebraMap (P₀.B₀ ⧸ 𝔭) (TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭)) d' = (1 : (FractionRing ↥S)) ⊗ₜ d' := fun _ => rfl
    have hd : ῑ d = 0 := by
      have h1 := IsLocalization.mk'_spec (TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭)) d s
      have h2 := congrArg φ h1
      rw [map_mul, hz, zero_mul, halg, hφ_tmul, map_one, one_mul] at h2
      exact h2.symm
    have : d = 0 := hῑ_inj (by rw [hd, map_zero])
    rw [this, IsLocalization.mk'_zero]

  haveI : Algebra.FiniteType ↥S P₀.B₀ := Algebra.FiniteType.of_restrictScalars_finiteType A ↥S P₀.B₀
  haveI : Module.Finite ↥S P₀.B₀ := Algebra.IsIntegral.finite
  haveI : Module.Finite ↥S (P₀.B₀ ⧸ 𝔭) := Module.Finite.of_surjective
    ((Ideal.Quotient.mkₐ ↥S 𝔭).toLinearMap) (Ideal.Quotient.mkₐ_surjective ↥S 𝔭)
  haveI : Module.Finite (FractionRing ↥S) (TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭)) := inferInstance
  have hφ_surj : Function.Surjective φ := by

    have hinv : ∀ u : ↥K, u ∈ Set.range φ → u ≠ 0 → u⁻¹ ∈ Set.range φ := by
      rintro u ⟨z, rfl⟩ hu

      let mz : TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭) →ₗ[(FractionRing ↥S)] TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭) := LinearMap.mulLeft (FractionRing ↥S) z
      have hmz_inj : Function.Injective mz := by
        intro a b hab
        have : φ z * φ a = φ z * φ b := by
          rw [← map_mul, ← map_mul]; exact congrArg φ hab
        exact hφ_inj (mul_left_cancel₀ hu this)
      obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hmz_inj) 1
      refine ⟨w, ?_⟩
      have : φ z * φ w = 1 := by rw [← map_mul]; exact (congrArg φ hw).trans (map_one φ)
      exact (eq_inv_of_mul_eq_one_right this)
    intro k
    obtain ⟨a, b, hb, hk⟩ := hdense k
    have ha : ι a ∈ Set.range φ := ⟨(1 : (FractionRing ↥S)) ⊗ₜ Ideal.Quotient.mk 𝔭 a, by rw [hφ_tmul, map_one, one_mul, hῑ_mk]⟩
    have hb' : ι b ∈ Set.range φ := ⟨(1 : (FractionRing ↥S)) ⊗ₜ Ideal.Quotient.mk 𝔭 b, by rw [hφ_tmul, map_one, one_mul, hῑ_mk]⟩
    obtain ⟨za, hza⟩ := ha
    obtain ⟨zb, hzb⟩ := hinv _ hb' hb
    refine ⟨za * zb, ?_⟩
    rw [map_mul, hza, hzb]
    have : k = P₀.classify x a * (P₀.classify x b)⁻¹ := by
      rw [← hk, mul_assoc, mul_inv_cancel₀ hb, mul_one]
    rw [this]
  let eφ : TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭) ≃ₗ[(FractionRing ↥S)] ↥K := (AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).toLinearEquiv

  set E : IntermediateField L ↥K := IntermediateField.adjoin L ({y} : Set ↥K) with hE
  have hSE : ∀ s : ↥S, ι (s : P₀.B₀) ∈ E := by
    intro s
    have hle : Algebra.adjoin A ({P₀.j₀} : Set P₀.B₀) ≤ (E.toSubalgebra.restrictScalars A).comap ι := by
      rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
      show ι P₀.j₀ ∈ E
      rw [hE]; exact IntermediateField.mem_adjoin_simple_self L y
    exact hle s.2
  have hFE : ∀ f : (FractionRing ↥S), FK f ∈ E := by
    intro f
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ↥S) f
    rw [map_div₀, hFK, hFK]
    exact div_mem (hSE a) (hSE b)
  have hEF : ∀ k : ↥K, k ∈ E → k ∈ Set.range FK := by

    have hAmem : ∀ a : A, algebraMap A ↥K a ∈ FK.fieldRange := by
      intro a
      refine ⟨algebraMap ↥S (FractionRing ↥S) ⟨algebraMap A P₀.B₀ a, S.algebraMap_mem a⟩, ?_⟩
      rw [hFK]
      exact ι.commutes a
    have hLmem : ∀ l : L, algebraMap L ↥K l ∈ FK.fieldRange := by
      intro l
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) l
      rw [map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      exact div_mem (hAmem a) (hAmem b)
    let E' : IntermediateField L ↥K := FK.fieldRange.toIntermediateField hLmem
    have hyE' : y ∈ E' := by
      show y ∈ FK.fieldRange
      refine ⟨algebraMap ↥S (FractionRing ↥S) ⟨P₀.j₀, Algebra.self_mem_adjoin_singleton A P₀.j₀⟩, ?_⟩
      rw [hFK]
    have hEE' : E ≤ E' := by
      rw [hE]; exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hyE')
    intro k hk
    exact hEE' hk
  let i₀ : (FractionRing ↥S) →+* ↥E := FK.codRestrict E hFE
  have hi₀_bij : Function.Bijective i₀ := by
    refine ⟨fun a b h => FK.injective (congrArg Subtype.val h : FK a = FK b), fun e => ?_⟩
    obtain ⟨f, hf⟩ := hEF e.1 e.2
    exact ⟨f, Subtype.ext hf⟩
  let i : (FractionRing ↥S) ≃+* ↥E := RingEquiv.ofBijective i₀ hi₀_bij
  have key : Module.finrank (FractionRing ↥S) (TensorProduct ↥S (FractionRing ↥S) (P₀.B₀ ⧸ 𝔭)) =
      Module.finrank ↥(IntermediateField.adjoin L ({y} : Set ↥K)) ↥K := by
    rw [eφ.finrank_eq]
    refine Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl ↥K) ?_
    ext f
    rfl
  exact key.trans hD2

end S_ModularCurve_FullLevel_Diamond_finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_finrank_fractionRing_tensorProduct_quotient_ker_classify_eq_of_dense_rigidDataH1Pow (solution)
