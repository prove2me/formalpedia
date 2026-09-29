-- Prove2me | solution 1 for ModularCurve.FullLevel.Diamond.snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/3753d662-92de-54e2-948a-f081be1c7d74

import Theorems.Thm_ModularCurve_IsGamma0PowAt_existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_ModularCurve_IsGamma1Point_existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
import Theorems.Thm_WeierstrassCurve_DrinfeldGlobal_existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
import Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero
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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_Diamond_snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Generic.isElliptic_curve ModularCurve.LevelP.instCommRingUnivBase ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatIntPDeltaUnivBase ModularCurve.LevelP.instCommRingTorsionPointRing ModularCurve.LevelP.instCommRingPsiRoot ModularCurve.LevelP.instIsScalarTowerTwoPointRingBasisRing ModularCurve.LevelP.instAlgebraPsiRoot ModularCurve.LevelP.instIsScalarTowerPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraMvPolynomialFinOfNatNatIntUnivBase ModularCurve.LevelP.instAlgebraTwoPointRing ModularCurve.LevelP.instIsScalarTowerTorsionPointRingTwoPointRing ModularCurve.LevelP.instAwayTwoPointRingIndepDenomBasisRing ModularCurve.LevelP.instCommRingBasisRing ModularCurve.LevelP.instAlgebraTorsionPointRing ModularCurve.LevelP.instAlgebraPsiRootTorsionPointRing ModularCurve.LevelP.instAlgebraBasisRing ModularCurve.LevelP.instAlgebraTwoPointRingBasisRing ModularCurve.LevelP.instCommRingVCRing ModularCurve.LevelP.instCommRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelPRing ModularCurve.LevelP.instAlgebraUnivBasisRingBorelRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelQRingBorelPRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingVCPolyVCRing ModularCurve.LevelP.instAwayMvPolynomialFinOfNatNatUnivBasisRingXVCRing ModularCurve.LevelP.instIsScalarTowerUnivBasisRingBorelPRingBorelRing ModularCurve.LevelP.instAlgebraUnivBasisRingVCRing ModularCurve.LevelP.instAlgebraVCPolyVCRing ModularCurve.LevelP.instAlgebraBorelPRingBorelRing ModularCurve.LevelP.instAwayBorelPRingBorelDenomBorelRing WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Generic.poly_map_classify WeierstrassCurve.Generic.poly_a₆ WeierstrassCurve.Generic.poly_a₁ WeierstrassCurve.Generic.classify_X WeierstrassCurve.Generic.coeffs_two WeierstrassCurve.Generic.coeffs_one WeierstrassCurve.Generic.curve_a₄"
p2m_attr_erase "simp" "WeierstrassCurve.Generic.coeffs_three WeierstrassCurve.Generic.poly_a₄ WeierstrassCurve.Generic.poly_a₃ WeierstrassCurve.Generic.poly_a₂ WeierstrassCurve.Generic.coeffs_zero WeierstrassCurve.Generic.curve_a₂ WeierstrassCurve.Generic.coeffs_four WeierstrassCurve.Generic.curve_a₆ WeierstrassCurve.Generic.curve_a₁ WeierstrassCurve.Generic.curve_a₃ ModularCurve.KatzLevelPForm.evalUniv_neg ModularCurve.KatzLevelPForm.evalUniv_mul ModularCurve.KatzLevelPForm.evalUniv_zero ModularCurve.KatzLevelPForm.evalUniv_sub ModularCurve.KatzLevelPForm.evalUniv_add ModularCurve.LevelP.VCRing.lift_vcVar ModularCurve.LevelP.BorelPRing.lift_xQ ModularCurve.LevelP.twoPointLift_xQ ModularCurve.LevelP.PsiRoot.lift_ofBase ModularCurve.LevelP.univVC_u ModularCurve.LevelP.twoPointLift_yP ModularCurve.LevelP.univVC_r ModularCurve.LevelP.TorsionPointRing.lift_torsionPtX ModularCurve.LevelP.TorsionPointRing.lift_ofPsiRoot ModularCurve.LevelP.TorsionPointRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_C ModularCurve.LevelP.BorelQRing.lift_of ModularCurve.LevelP.BorelPRing.lift_yQ ModularCurve.LevelP.BorelPRing.lift_ofUniv ModularCurve.LevelP.univVC_t ModularCurve.LevelP.BorelRing.lift_ofUniv ModularCurve.LevelP.univVC_s ModularCurve.LevelP.twoPointLift_xP ModularCurve.LevelP.twoPointLift_yQ ModularCurve.LevelP.TorsionPointRing.lift_torsionPtY ModularCurve.LevelP.BorelQRing.lift_borelQY ModularCurve.LevelP.VCRing.lift_algebraMap ModularCurve.LevelP.VCRing.lift_ofUniv ModularCurve.LevelP.PsiRoot.lift_psiRootX ModularCurve.LevelP.BorelRing.lift_algebraMap"
p2m_attr_erase "simp" "ModularCurve.LevelP.BorelPRing.lift_yP ModularCurve.LevelP.BasisRing.lift_ofTwoPoint ModularCurve.LevelP.BasisRing.lift_ofBase ModularCurve.LevelP.vcPolyLift_X ModularCurve.LevelP.genericLift_X ModularCurve.LevelP.twoPointLift_ofBase ModularCurve.LevelP.BorelPRing.lift_xP WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X WeierstrassProjModel.kw_lrThird_substHom_X WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.RelativeGroupLaw.actionSndPoint_coe GoodReductionJacobian.RelativeGroupLaw.actionFstPoint_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (A : Type) [CommRing A]
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
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (t : Ω) (ht : Transcendental ℚ t) :
    ∀ φ : P₀.B₀ →ₐ[A] DualNumber Ω,
      φ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf P₀.univ) = algebraMap Ω (DualNumber Ω) t →
        ∀ b : P₀.B₀, (φ b).snd = 0 := by
  classical
  intro φ hφ b

  set fstA : DualNumber Ω →ₐ[A] Ω := (TrivSqZeroExt.fstHom Ω Ω Ω).restrictScalars A with hfstA
  set inlA : Ω →ₐ[A] DualNumber Ω := (TrivSqZeroExt.inlAlgHom Ω Ω Ω).restrictScalars A with hinlA
  have hfst_toRingHom : fstA.toRingHom = (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom := rfl
  have hinl_toRingHom : inlA.toRingHom = algebraMap Ω (DualNumber Ω) := RingHom.ext fun a => rfl
  have hfst_inl : fstA.toRingHom.comp inlA.toRingHom = RingHom.id Ω := RingHom.ext fun a => rfl
  have hfst_inlA : fstA.comp inlA = AlgHom.id A Ω := AlgHom.ext fun a => rfl

  suffices key : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map (inlA.comp fstA) ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ) =
      (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ by
    have key' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map ((inlA.comp fstA).comp φ) P₀.univ = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ := by
      rw [(rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map_comp]; exact key
    have huniq := (P₀.represents (DualNumber Ω) ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ)).unique key' rfl
    have hb : ((inlA.comp fstA).comp φ) b = φ b := by rw [huniq]
    rw [← hb]
    exact TrivSqZeroExt.snd_inl (M := Ω) _

  have hjx : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ) = algebraMap Ω (DualNumber Ω) t := by
    rw [(rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.jOf_map]; exact hφ
  generalize (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum.map φ P₀.univ = x at hjx ⊢
  obtain ⟨r, rfl⟩ := Quot.exists_rep x

  change ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).curve r).jOfUnit ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).isUnit_Δ r) = algebraMap Ω (DualNumber Ω) t at hjx
  set W : WeierstrassCurve (DualNumber Ω) := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).curve r with hWdef
  have hΔW : IsUnit W.Δ := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).isUnit_Δ r
  set W₀ : WeierstrassCurve Ω := W.map fstA.toRingHom with hW₀def
  have hΔW₀ : IsUnit W₀.Δ := W.isUnit_Δ_map _ hΔW
  haveI hEW : W.IsElliptic := ⟨hΔW⟩
  haveI hEW₀ : W₀.IsElliptic := ⟨hΔW₀⟩
  have hjW : W.j = algebraMap Ω (DualNumber Ω) t := by
    rw [← W.jOfUnit_eq_j hΔW]; exact hjx
  have hjW₀ : W₀.j = t := by
    rw [← W₀.jOfUnit_eq_j hΔW₀]
    have h := W.jOfUnit_map fstA.toRingHom hΔW hΔW₀
    rw [hjx] at h
    simp at h
    exact h

  have ht0 : W₀.j ≠ 0 := by
    rw [hjW₀]; rintro h0; exact ht (h0 ▸ isAlgebraic_zero)
  have ht1728 : W₀.j ≠ 1728 := by
    rw [hjW₀]; rintro h1
    apply ht; rw [h1]
    have : (1728 : Ω) = algebraMap ℚ Ω 1728 := by simp
    rw [this]; exact isAlgebraic_algebraMap _
  have h2 : (2 : Ω) ≠ 0 := by norm_num
  have h3 : (3 : Ω) ≠ 0 := by norm_num
  have hjsnd : TrivSqZeroExt.snd W.j = 0 := by
    rw [hjW, TrivSqZeroExt.algebraMap_eq_inl']; exact TrivSqZeroExt.snd_inl (M := Ω) _

  obtain ⟨C, hC1, hCW⟩ :=
    WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero Ω h2 h3 W₀ ht0 ht1728 W
      (by rw [hW₀def, hfst_toRingHom]) hjsnd
  rw [← hinl_toRingHom] at hCW

  set E : WeierstrassCurve (DualNumber Ω) := W₀.map inlA.toRingHom with hEdef
  have hΔE : IsUnit E.Δ := W₀.isUnit_Δ_map _ hΔW₀
  have hEfst : E.map fstA.toRingHom = W₀ := by
    rw [hEdef, WeierstrassCurve.map_map, hfst_inl, WeierstrassCurve.map_id]
  have hEconst : (E.map fstA.toRingHom).map inlA.toRingHom = E := by rw [hEfst]

  set r' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Raw (DualNumber Ω) := (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C⁻¹ r with hr'def
  have hcurve' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).curve r' = E := by
    rw [hr'def, (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).curve_act]
    change C⁻¹ • W = E
    rw [← hCW, smul_smul, inv_mul_cancel, one_smul]

  have hunitε : ∀ n : ℕ, IsUnit ((n : ℕ) : A) → IsUnit ((n : ℕ) : DualNumber Ω) := fun n hn => by
    have := hn.map (algebraMap A (DualNumber Ω)); rwa [map_natCast] at this
  have hM'ε := hunitε M' hM'A
  have hℓε := hunitε ℓg hℓA
  have hqε : IsUnit ((q : ℕ) : DualNumber Ω) := by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.fst_natCast]; exact isUnit_iff_ne_zero.mpr hqΩ
  have hqΩ' : IsUnit ((q : ℕ) : Ω) := isUnit_iff_ne_zero.mpr hqΩ
  have hℓg3 : 3 ≤ ℓg := by omega

  have hsurj : Function.Surjective fstA.toRingHom := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hnil : ∃ n : ℕ, RingHom.ker fstA.toRingHom ^ n = ⊥ := by
    refine ⟨2, ?_⟩
    rw [show RingHom.ker fstA.toRingHom ^ 2 = RingHom.ker fstA.toRingHom * RingHom.ker fstA.toRingHom from pow_two _,
      eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    rw [Ideal.mem_bot]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [TrivSqZeroExt.fst_mul, hx, zero_mul, TrivSqZeroExt.fst_zero]
    · rw [DualNumber.snd_mul, hx, hy, zero_mul, mul_zero, add_zero, TrivSqZeroExt.snd_zero]

  have main : r' = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing inlA ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing fstA r') := by

    have hlev := r'.isLevel
    have hcurveE : r'.curve = E := hcurve'
    obtain ⟨⟨hh, hD, hx⟩, -⟩ := hlev
    rw [hcurveE] at hh hD hx
    apply ModularCurve.LevelComponent.Raw.ext'
    · show r'.curve = (r'.curve.map fstA.toRingHom).map inlA.toRingHom
      rw [hcurveE, hEconst]
    · show r'.level = ((fun p => ((r'.level.1 p).map fstA.toRingHom).map inlA.toRingHom),
          ((r'.level.2.1.map fstA.toRingHom).map inlA.toRingHom, 𝒯.map inlA (𝒯.map fstA r'.level.2.2)))
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      ·
        have hu := ModularCurve.IsGamma0PowAt.existsUnique_tuple_map_eq_of_surjective_of_ker_pow_eq_bot
          fstA.toRingHom hsurj hnil E hΔE M' hM'ε (fun p => (r'.level.1 p).map fstA.toRingHom)
          (fun p => ModularCurve.IsGamma0PowAt.map fstA.toRingHom E _ _ (hh p))
        refine hu.unique ⟨rfl, hh⟩ ⟨?_, ?_⟩
        · funext p
          show (((r'.level.1 p).map fstA.toRingHom).map inlA.toRingHom).map fstA.toRingHom = _
          rw [Polynomial.map_map, hfst_inl, Polynomial.map_id]
        · intro p
          have := ModularCurve.IsGamma0PowAt.map inlA.toRingHom (E.map fstA.toRingHom) (p : ℕ)
            (M'.factorization (p : ℕ)) (ModularCurve.IsGamma0PowAt.map fstA.toRingHom E _ _ (hh p))
          rwa [hEconst] at this
      ·
        have hu := ModularCurve.IsGamma1Point.existsUnique_map_eq_of_surjective_of_ker_pow_eq_bot
          fstA.toRingHom hsurj hnil E hΔE ℓg hℓg hℓg3 hℓε (r'.level.2.1.map fstA.toRingHom) (hD.map fstA.toRingHom)
        refine hu.unique ⟨rfl, hD⟩ ⟨?_, ?_⟩
        · rw [ModularCurve.LevelPData.map_map, hfst_inl, ModularCurve.LevelPData.map_id]
        · have := (hD.map fstA.toRingHom).map inlA.toRingHom
          rwa [hEconst] at this
      ·
        set z : RawDrinfeldPair (DualNumber Ω) := r'.level.2.2 with hzdef
        set z₁ : RawDrinfeldPair Ω := 𝒯.map fstA z with hz₁def
        have hz₁ : RawDrinfeldPair.IsLevel 𝒢 q (E.map fstA.toRingHom) z₁ := 𝒯.isLevel_map fstA E z hx
        have hz₁' : RawDrinfeldPair.IsLevel 𝒢 q W₀ z₁ := by rwa [hEfst] at hz₁
        set y : RawDrinfeldPair (DualNumber Ω) := 𝒯.map inlA z₁ with hydef
        have hy : RawDrinfeldPair.IsLevel 𝒢 q (W₀.map inlA.toRingHom) y := 𝒯.isLevel_map inlA W₀ z₁ hz₁'
        have hyE : RawDrinfeldPair.IsLevel 𝒢 q E y := hy
        have hyfst : 𝒯.map fstA y = z₁ := by
          rw [hydef, ← 𝒯.map_comp, hfst_inlA, 𝒯.map_id]
        have hsurj' : Function.Surjective fstA := fun a => hsurj a
        have hu := WeierstrassCurve.DrinfeldGlobal.existsUnique_isLevel_map_eq_of_surjective_of_ker_pow_eq_bot_of_isUnit
          q A 𝒢 h𝒢 h𝒢O 𝒯 h𝒯 fstA hsurj' hnil E hΔE hqε z₁ hz₁
        have hxz : RawDrinfeldPair.IsLevel 𝒢 q E z := hx
        show z = 𝒯.map inlA (𝒯.map fstA z)
        exact hu.unique ⟨hxz, rfl⟩ ⟨hyE, hyfst⟩

  have hr : r = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (inlA.comp fstA) r) := by
    have h1 : r = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act C r' := by rw [hr'def, ← (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_mul, mul_inv_cancel, (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_one]
    have h2' : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing fstA r' = (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing fstA r := by
      rw [hr'def, (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing_act]
      have : C⁻¹.map fstA.toRingHom = 1 := by
        rw [show C⁻¹.map fstA.toRingHom = WeierstrassCurve.VariableChange.mapHom fstA.toRingHom C⁻¹ from rfl, map_inv,
          show WeierstrassCurve.VariableChange.mapHom fstA.toRingHom C = C.map fstA.toRingHom from rfl,
          hfst_toRingHom, hC1, inv_one]
      rw [this, (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).act_one]
    conv_lhs => rw [h1, main, h2', ← (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing_comp]
  symm
  show (Quot.mk _ r : (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).Pt (DualNumber Ω)) = Quot.mk _ ((rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing (inlA.comp fstA) r)
  exact (Quot.sound ⟨C, hr⟩).symm

end S_ModularCurve_FullLevel_Diamond_snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow
end P2MW
export P2MW.S_ModularCurve_FullLevel_Diamond_snd_apply_eq_zero_of_apply_jOf_univ_eq_dualNumber_rigidDataH1Pow (solution)
