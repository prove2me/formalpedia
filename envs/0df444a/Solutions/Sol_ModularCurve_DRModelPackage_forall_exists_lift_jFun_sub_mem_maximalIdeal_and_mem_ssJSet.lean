-- Prove2me | solution 1 for ModularCurve.DRModelPackage.forall_exists_lift_jFun_sub_mem_maximalIdeal_and_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0ac4d08c-074f-53dc-882d-3788a93c3155

import Mathlib
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff
import Theorems.Thm_ModularCurve_inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed
import Definitions.Def_ModularCurve_DRResolvedModelCharts
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
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
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_forall_exists_lift_jFun_sub_mem_maximalIdeal_and_mem_ssJSet
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.HpoolLevelRing.instCommRingAfin ModularCurve.HpoolLevelRing.instCommRingLevelRing ModularCurve.HpoolLevelRing.instSMulAway ModularCurve.HpoolLevelRing.instModuleAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraAfinAfinAway ModularCurve.HpoolLevelRing.instModuleAway ModularCurve.HpoolLevelRing.instModuleLevelRing ModularCurve.HpoolLevelRing.instCommRingAfinAway ModularCurve.HpoolLevelRing.instModuleAfinSelf ModularCurve.HpoolLevelRing.instSMulAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraLevelRing ModularCurve.HpoolLevelRing.instAlgebraIntAfinAway ModularCurve.HpoolLevelRing.instIsDomainAfin ModularCurve.HpoolLevelRing.instAlgebraIntAfin ModularCurve.HpoolLevelRing.instSMulLevelRing ModularCurve.HpoolLevelRing.algebraAway ModularCurve.HpoolLevelRing.instAlgebraAfinAwayLevelRing ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian MvPolynomial MvPolynomial.CrossingQuotient ModularCurve~nodeEquiv AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in
set_option maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)
    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    [DecidableEq k]
    (hred : Function.Surjective red)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))
    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k) (htoκ : ∀ o : O, toκ o = red ⟨ιK (algebraMap O K o), hιA o⟩)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
    (hφO : ∀ (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (a : O),
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K a)))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hφj : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((φ ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField
          ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) :
            ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))
    :
    ∀ n : 𝔛reg.node, ∃ ĵ : O,
      (∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n))),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ))) ∧
      red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ ∈ ssJSet p k := by
  classical
  intro n
  let X : Scheme := (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
  let FB := ↥(modularFunctionFieldBar (1 * p))
  let xn : X := (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)

  obtain ⟨a, ha⟩ := ModularCurve.DRResolvedModelPackage.exists_node_equiv_ssJSet_germ_sub_mem_maximalIdeal_iff p hp 𝔛 O hϖO k toκ 𝔛reg
  obtain ⟨hU, hiff⟩ := ha n

  have hker : RingHom.ker red = IsLocalRing.maximalIdeal ↥A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective red hred)
  have hsurj : Function.Surjective toκ := by
    intro s
    obtain ⟨a', ha'⟩ := hred s
    obtain ⟨o, ho⟩ := (ModularCurve.inertiaField_comap_isDVR_and_residue_surjective_and_place_fixed p A hA 1).2.2.1
      (IsLocalRing.residue ↥A a')
    refine ⟨eO.symm o, ?_⟩
    rw [htoκ, ← ha']
    have e1 : (⟨ιK (algebraMap O K (eO.symm o)), hιA _⟩ : ↥A) = ⟨((o : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ), o.2⟩ :=
      Subtype.ext (by show ιK (algebraMap O K (eO.symm o)) = ((o : ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))) : AlgebraicClosure ℚ); rw [hιK, RingEquiv.apply_symm_apply]; rfl)
    rw [e1, ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, hker, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact ho
  obtain ⟨ĵ, hĵ⟩ := hsurj ((a n : ↥(ssJSet p k)) : k)
  refine ⟨ĵ, ?_, ?_⟩
  ·
    have hmem := (hiff ĵ).mp hĵ
    refine ⟨_, hmem, ?_⟩
    haveI : Nonempty (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) : X.Opens) := ⟨⟨xn, hU⟩⟩
    have hgerm : ∀ (U : X.Opens) [Nonempty U] (y : X) (hy : y ∈ U) (s : Γ(X, U)),
        algebraMap (X.presheaf.stalk y) ↥X.functionField ((X.presheaf.germ U y hy).hom s) = (X.germToFunctionField U).hom s := by
      intro U _ y hy s
      show (X.presheaf.germ U y hy ≫ X.presheaf.stalkSpecializes (genericPoint_specializes y)).hom s = _
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    have hj : φ (algebraMap _ ↥X.functionField ((X.presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) xn hU).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
          (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) =
        ProlongationTuple.jFun 1 p := by
      apply Subtype.ext; rw [hgerm, hφj]; rfl
    rw [map_sub, map_sub, hj, hφO]
  ·
    have : red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = toκ ĵ := (htoκ ĵ).symm
    rw [this, hĵ]
    exact (a n).2

end S_ModularCurve_DRModelPackage_forall_exists_lift_jFun_sub_mem_maximalIdeal_and_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_forall_exists_lift_jFun_sub_mem_maximalIdeal_and_mem_ssJSet (solution)
