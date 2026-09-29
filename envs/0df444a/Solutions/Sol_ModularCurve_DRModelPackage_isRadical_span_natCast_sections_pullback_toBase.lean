-- Prove2me | solution 1 for ModularCurve.DRModelPackage.isRadical_span_natCast_sections_pullback_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8c3f2f0d-38cb-5705-a6d5-b5b9706cefcf

import Mathlib
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Theorems.Thm_ModularCurve_DRModel_isReduced_pullback_toBase_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_isRadical_span_natCast_sections_pullback_toBase
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
p2m_attr_erase "simp" "GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve P2MW.S_ModularCurve_DRModelPackage_isRadical_span_natCast_sections_pullback_toBase.ModularCurve TensorProduct"

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRModel DRModel.toBase DRModelPackage DRModel.isReduced_pullback_toBase_of_charP"
namespace DRModelPackage
p2m_export "ModularCurve.DRModelPackage" "mk"
namespace Radical
p2m_open "ModularCurve.DRModelPackage ModularCurve"

variable (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]

theorem isPullback_baseChangeMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    IsPullback (DRModel.baseChangeMap (p := p) φ)
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  have hρι : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show φ.comp (algebraMap ℤ A) = algebraMap ℤ B from RingHom.ext_int _ _]
  have h2 : DRModel.baseChangeMap (p := p) φ ≫ pullback.snd (DRModel.toBase p) _ =
      pullback.snd (DRModel.toBase p) _ ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ h2
    (IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))))
  have h1 : DRModel.baseChangeMap (p := p) φ ≫ pullback.fst (DRModel.toBase p) _ =
      pullback.fst (DRModel.toBase p) _ := by
    rw [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  convert IsPullback.of_hasPullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ B))) using 1

end ModularCurve.DRModelPackage.Radical

open ModularCurve.DRModelPackage.Radical in

theorem solution
    (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (hmax : (Ideal.span {((p : ℕ) : O)}).IsMaximal)
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).affineOpens) :
    (Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U))}).IsRadical := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  letI : (Ideal.span {((p : ℕ) : O)}).IsMaximal := hmax
  haveI : CharP (O ⧸ Ideal.span {((p : ℕ) : O)}) p := CharP.quotient O p fun hu => hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span rfl) hu)

  haveI hred : IsReduced (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (O ⧸ Ideal.span {((p : ℕ) : O)}))))) := by
    have h := @ModularCurve.DRModel.isReduced_pullback_toBase_of_charP p _ _ (O ⧸ Ideal.span {((p : ℕ) : O)}) (Ideal.Quotient.field _) inferInstance
    exact h
  let jres : Spec (CommRingCat.of (O ⧸ Ideal.span {((p : ℕ) : O)})) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)})))
  have hPB := isPullback_baseChangeMap p (Ideal.Quotient.mk (Ideal.span {((p : ℕ) : O)}))
  haveI : IsReduced (pullback (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) jres) :=
    @isReduced_of_isOpenImmersion _ _ (hPB.isoPullback).inv inferInstance hred

  let g : Spec (CommRingCat.of Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U)) ⟶ Spec (CommRingCat.of O) :=
    U.2.fromSpec ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))
  let ψ : CommRingCat.of O ⟶ CommRingCat.of Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) := (Scheme.Spec.preimage g).unop
  have hψ : Spec.map ψ = g := Scheme.Spec.map_preimage g
  letI : Algebra O Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) := ψ.hom.toAlgebra

  have e1 : pullback (Spec.map (CommRingCat.ofHom (algebraMap O Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U)))) (Spec.map (CommRingCat.ofHom (algebraMap O (O ⧸ Ideal.span {((p : ℕ) : O)})))) ≅
      pullback g jres := pullback.congrHom (by rw [← hψ]; rfl) rfl
  let e2 := pullbackRightPullbackFstIso (pullback.snd (DRModel.toBase p)
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) jres U.2.fromSpec

  haveI : IsReduced (pullback U.2.fromSpec (pullback.fst (pullback.snd (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) jres)) :=
    isReduced_of_isOpenImmersion (pullback.snd U.2.fromSpec (pullback.fst (pullback.snd (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) jres))
  haveI : IsReduced (Spec (CommRingCat.of (Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) ⊗[O] (O ⧸ Ideal.span {((p : ℕ) : O)})))) :=
    isReduced_of_isOpenImmersion ((pullbackSpecIso O Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) (O ⧸ Ideal.span {((p : ℕ) : O)})).inv ≫ e1.hom ≫ e2.inv)
  have hAk : _root_.IsReduced (Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) ⊗[O] (O ⧸ Ideal.span {((p : ℕ) : O)})) := (affine_isReduced_iff (CommRingCat.of (Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) ⊗[O] (O ⧸ Ideal.span {((p : ℕ) : O)})))).mp inferInstance

  rw [Ideal.isRadical_iff_quotient_reduced]
  change _root_.IsReduced (Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) ⧸ Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U))})
  have hmap : Ideal.map (algebraMap O Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U)) (Ideal.span {((p : ℕ) : O)}) = Ideal.span {((p : ℕ) : Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U))} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact isReduced_of_injective _ (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Γ(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))), U) (Ideal.span {((p : ℕ) : O)})).injective

end S_ModularCurve_DRModelPackage_isRadical_span_natCast_sections_pullback_toBase
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_isRadical_span_natCast_sections_pullback_toBase (solution)
