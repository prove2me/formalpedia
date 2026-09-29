-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/284fd870-0c2b-5a94-a94b-e06998985f04

import Mathlib
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
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModelCharts
import Theorems.Thm_ModularCurve_DRModel_exists_chartAlgFin_valuationSubring_pair_levelP
import Theorems.Thm_ModularCurve_DRModelPackage_compl_jNeLocus_inter_range_comp_eq_singleton
import Theorems.Thm_ModularCurve_DRModel_exists_ne_and_notMem_chartFin_pFibre
import Theorems.Thm_ModularCurve_DRModelPackage_exists_range_comp_subset_zeroLocus_jq_sub_pow

import Theorems.Thm_ModularCurve_DRResolvedModelPackage_exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
import Theorems.Thm_ModularCurve_placeEquiv_unique_and_arithmeticGalois_smul_of_forall_mem_iff
import Theorems.Thm_AlgebraicCurve_Place_evalAt_congr
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.GaussReduction.isLocalHom_constToGauss"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing ModularCurve.PlaceSpecialization

namespace HorSwapG

theorem exists_chartAlgFin_coe_eq_qExpand_sub_pow (p : ℕ) [Fact p.Prime] :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)), ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨jp, W₀, W₁, hjp, -⟩ := ModularCurve.DRModel.exists_chartAlgFin_valuationSubring_pair_levelP p
  refine ⟨jp - TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ^ p, ?_⟩
  rw [Subalgebra.coe_sub, Subalgebra.coe_pow, TwoChartIntegralModel.coe_jChartFin, AddSubgroupClass.coe_sub,
    SubmonoidClass.coe_pow, hjp, IgusaScheme.coe_jFull]

theorem phi_algebraMap_germ_eq_jQFun_sub_pow (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
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
    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (ha : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p)
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hx : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) x hx).hom
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))) =
      ProlongationTuple.jQFun 1 p - ProlongationTuple.jFun 1 p ^ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hgerm : algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) x hx).hom
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) =
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).germToFunctionField ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) := by
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rw [hgerm]
  apply Subtype.ext
  rw [hφj a, ha, map_sub, map_pow]
  rfl

theorem phi_algebraMap_germ_eq_jFun (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+* ↥(modularFunctionFieldBar (1 * p)))
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
    (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hx : x ∈ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk x) ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField)
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) x hx).hom
        (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) =
      ProlongationTuple.jFun 1 p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  apply Subtype.ext
  rw [hφj, TwoChartIntegralModel.coe_jChartFin, IgusaScheme.coe_jFull]
  rfl

end HorSwapG

namespace FinJ

theorem mem_chartFinOpenBC_iff (p : ℕ) [Fact p.Prime] [NeZero p] (k : Type) [Field k]
    (y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) :
    y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k ↔
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y ∈ TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) ↔ _
  rw [← TwoChartIntegralModel.TwoChartsAux.U_eq]

theorem compInf_fst_mem_chartFinOpenBC_of_two_cusps (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p)
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (hcusps : ∃ y₁ y₂ : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y₁ ≠ y₂ ∧
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₁ ∉ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ∧ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base y₂ ∉ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
    (c : ↥(pullback (𝔛.compInf k) (𝔛.compZero k))) :
    (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) ∈
      TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨xI, hxI⟩ := (ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton p 𝔛 k (𝔛.compInf k) (Or.inl rfl)).2
  obtain ⟨xZ, hxZ⟩ := (ModularCurve.DRModelPackage.compl_jNeLocus_inter_range_comp_eq_singleton p 𝔛 k (𝔛.compZero k) (Or.inr rfl)).2

  have hL : ∀ y : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), y ∉ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k →
      y = (𝔛.compInf k).base xI.1 ∨ y = (𝔛.compZero k).base xZ.1 := by
    intro y hy
    rcases 𝔛.comp_jointly_surjective k y with h | h
    · left
      have : y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compInf k).base := ⟨hy, h⟩
      rw [hxI] at this
      exact this
    · right
      have : y ∈ ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compZero k).base := ⟨hy, h⟩
      rw [hxZ] at this
      exact this

  have hne : (𝔛.compInf k).base xI.1 ≠ (𝔛.compZero k).base xZ.1 := by
    obtain ⟨y₁, y₂, h12, h1, h2⟩ := hcusps
    rw [← mem_chartFinOpenBC_iff] at h1 h2
    rcases hL y₁ h1 with rfl | rfl <;> rcases hL y₂ h2 with rfl | rfl
    · exact absurd rfl h12
    · exact h12
    · exact fun e => h12 e.symm
    · exact absurd rfl h12

  by_contra hy
  have h1 : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) = (𝔛.compInf k).base xI.1 := by
    have : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) ∈
        ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compInf k).base := ⟨hy, ⟨_, rfl⟩⟩
    rw [hxI] at this
    exact this
  have h2 : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) = (𝔛.compZero k).base xZ.1 := by
    have hcond : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) =
        (𝔛.compZero k).base ((pullback.snd (𝔛.compInf k) (𝔛.compZero k)).base c) := by
      rw [← TopCat.comp_app, ← TopCat.comp_app, ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, pullback.condition]
    have : (𝔛.compInf k).base ((pullback.fst (𝔛.compInf k) (𝔛.compZero k)).base c) ∈
        ((TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k :
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).Opens) :
          Set ↥(TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k))ᶜ ∩
          Set.range (𝔛.compZero k).base := ⟨hy, ⟨_, hcond.symm⟩⟩
    rw [hxZ] at this
    exact this
  exact hne (h1.symm.trans h2)

end FinJ

namespace HorSwapG

theorem node_mem_preimage_chartFin
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k)
    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ) (n : 𝔛reg.node) :
    ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv n)) ∈
      (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := FinJ.compInf_fst_mem_chartFinOpenBC_of_two_cusps p 𝔛 k
    (ModularCurve.DRModel.exists_ne_and_notMem_chartFin_pFibre p hp k) (𝔛reg.nodeEquiv n)
  rw [FinJ.mem_chartFinOpenBC_iff] at h
  have hcomp : (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ) ≫
      pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫
        (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
    simp only [Category.assoc, DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  have key := congrArg (fun g => g.base (𝔛reg.nodeEquiv n)) hcomp
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at key
  change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base _ ∈
    ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h ⊢
  convert h using 2

end HorSwapG

namespace HorSwapG

theorem stalkClosedPointTo_germ_top {X : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (s : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo f).hom ((X.presheaf.germ ⊤ (f.base (closedPoint R)) trivial).hom s) =
      (Scheme.ΓSpecIso R).hom (f.appTop.hom s) := by
  have h := Scheme.germ_stalkClosedPointTo f ⊤ trivial
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom] at h'
  rw [h']
  congr 1

theorem eval_const (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (ℓ : Spec (CommRingCat.of k) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
    (hℓ : ℓ ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) = 𝟙 _) (c₀ : k) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    (Scheme.stalkClosedPointTo ℓ).hom
      (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ⊤ (ℓ.base (IsLocalRing.closedPoint k)) trivial).hom
        (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c₀)) = c₀ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [stalkClosedPointTo_germ_top]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom (ℓ.appTop.hom
    (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c₀))) = c₀
  have happ : (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).appTop ≫ ℓ.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hℓ, Scheme.Hom.id_appTop]
  change (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).appTop ≫ ℓ.appTop) ≫
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c₀) = c₀
  rw [happ, Category.id_comp, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

theorem stalkClosedPointTo_SpecMap_germ {R S : CommRingCat.{0}} [IsLocalRing R] [IsLocalRing S] (φ : R ⟶ S) [IsLocalHom φ.hom]
    (V : (Spec R).Opens) (hV : V = ⊤) (y : Γ(Spec R, V))
    (h₁ : (Spec.map φ).base (closedPoint S) ∈ V) (h₂ : closedPoint R ∈ V) :
    (Scheme.stalkClosedPointTo (Spec.map φ)).hom (((Spec R).presheaf.germ V ((Spec.map φ).base (closedPoint S)) h₁).hom y) =
      φ.hom ((stalkClosedPointIso R).hom.hom (((Spec R).presheaf.germ V (closedPoint R) h₂).hom y)) := by
  subst hV
  have e1 := congrArg (fun f => f.hom y) (Scheme.germ_stalkClosedPointTo_Spec (R := R) (S := S) φ)
  have e2 := congrArg (fun f => f.hom y) (germ_stalkClosedPointIso_hom (R := R))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e1 e2
  erw [e1, e2]

theorem eval_comp (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsLocalRing O] (k : Type) [Field k]
    (toκ : O →+* k) [IsLocalHom toκ]
    (s : Spec (CommRingCat.of O) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (ℓ : Spec (CommRingCat.of k) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))))
    (hℓbc : ℓ ≫ (DRModel.baseChangeMap toκ) = Spec.map (CommRingCat.ofHom toκ) ≫ s)
    (U : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Opens) (G : Γ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))), U))
    (hU : (ℓ ≫ (DRModel.baseChangeMap toκ)).base (IsLocalRing.closedPoint k) ∈ U)
    (hU' : s.base (IsLocalRing.closedPoint O) ∈ U) :
    (Scheme.stalkClosedPointTo (ℓ ≫ (DRModel.baseChangeMap toκ))).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ U _ hU).hom G) =
      toκ ((Scheme.stalkClosedPointTo s).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ U _ hU').hom G)) := by
  suffices key : ∀ (t : Spec (CommRingCat.of k) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (ht : t.base (IsLocalRing.closedPoint k) ∈ U),
      t = Spec.map (CommRingCat.ofHom toκ) ≫ s →
      (Scheme.stalkClosedPointTo t).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ U _ ht).hom G) =
        toκ ((Scheme.stalkClosedPointTo s).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ U _ hU').hom G)) from key _ hU hℓbc
  intro t ht e
  subst e
  haveI : IsLocalHom (CommRingCat.ofHom toκ).hom := ‹IsLocalHom toκ›
  have hpt : (Spec.map (CommRingCat.ofHom toκ)).base (closedPoint k) = closedPoint O := Spec_closedPoint

  rw [Scheme.stalkClosedPointTo_comp]
  change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom toκ))).hom
      ((s.stalkMap ((Spec.map (CommRingCat.ofHom toκ)).base (closedPoint k))).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ U (s.base ((Spec.map (CommRingCat.ofHom toκ)).base (closedPoint k))) ht).hom G)) =
    toκ ((stalkClosedPointIso (CommRingCat.of O)).hom.hom ((s.stalkMap (closedPoint O)).hom
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ U (s.base (closedPoint O)) hU').hom G)))
  erw [Scheme.Hom.germ_stalkMap_apply s U ((Spec.map (CommRingCat.ofHom toκ)).base (closedPoint k)) ht,
    Scheme.Hom.germ_stalkMap_apply s U (closedPoint O) hU']
  have hV : s ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem s hU'
  exact stalkClosedPointTo_SpecMap_germ (CommRingCat.ofHom toκ) (s ⁻¹ᵁ U) hV _ _ _

end HorSwapG

namespace HunrDR

theorem isPullback_baseChangeMap (p : ℕ) [Fact p.Prime] {O k : Type} [CommRing O] [CommRing k] (toκ : O →+* k) :
    IsPullback (DRModel.baseChangeMap (p := p) toκ)
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))
      (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))
      (Spec.map (CommRingCat.ofHom toκ)) := by
  have e1 : DRModel.baseChangeMap (p := p) toκ ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) := by
    simp only [DRModel.baseChangeMap, pullback.lift_fst, Category.comp_id]
  have e2 : Spec.map (CommRingCat.ofHom toκ) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ O)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ k)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext_int _ _
  have e3 : DRModel.baseChangeMap (p := p) toκ ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))) ≫ Spec.map (CommRingCat.ofHom toκ) := by
    simp only [DRModel.baseChangeMap, pullback.lift_snd]
  refine IsPullback.of_right ?_ e3 (IsPullback.of_hasPullback _ _)
  rw [e1, e2]
  exact IsPullback.of_hasPullback _ _

end HunrDR

namespace HorAtSwap

set_option maxHeartbeats 3200000 in

theorem main
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (𝔛 : DRModelPackage p)
    (O : Type) [CommRing O] [IsLocalRing O]
    (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (toκ : O →+* k) (hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O)
    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hPKG : ∃ (C D : (𝔛.ratModel k).C ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))),
      ((C = 𝔛.compInf k ∧ D = 𝔛.compZero k) ∨ (C = 𝔛.compZero k ∧ D = 𝔛.compInf k)) ∧

      (∀ y : ↥(𝔛.ratModel k).C, ∀ hy : C.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (C.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _) ∧

      (∀ y : ↥(𝔛.ratModel k).C, ∀ hy : D.base y ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (D.base y) hy).hom
          (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
            (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of
                ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ →
        ∃ c : k, c ^ (p ^ 2) = c ∧
          ∀ hy' : D.base y ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k,
            ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ
                (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) (D.base y) hy').hom
              (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
                (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op
                  (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c)) ∈
              IsLocalRing.maximalIdeal _))
    (swap : Bool)
    (s : Spec (CommRingCat.of O) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
    (hs : s ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = 𝟙 _)
    (hcin : s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ (DRModel.baseChangeMap toκ)).base)
    (hcout : s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ (DRModel.baseChangeMap toκ)).base)
    (hfin_c : s.base (IsLocalRing.closedPoint O) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))
    (hFc : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈
      IsLocalRing.maximalIdeal _)
    (hJc : toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) ^ (p ^ 2) ≠
      toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))))) :
    (swap = false → ∀ hη : (𝔛.compInf k ≫ (DRModel.baseChangeMap toκ)).base (genericPoint ↥(𝔛.ratModel k).C) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hη).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _) ∧
    (swap = true → ∀ hη : (𝔛.compZero k ≫ (DRModel.baseChangeMap toκ)).base (genericPoint ↥(𝔛.ratModel k).C) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hη).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  haveI hloc : IsLocalHom toκ := by
    refine ⟨fun o ho => ?_⟩
    by_contra hno
    have hmem : o ∈ RingHom.ker toκ := by rw [hker]; exact (IsLocalRing.mem_maximalIdeal _).mpr hno
    exact ho.ne_zero (RingHom.mem_ker.mp hmem)
  have hcl : (Spec.map (CommRingCat.ofHom toκ)).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint O :=
    IsLocalRing.comap_closedPoint toκ

  have Hsq := HunrDR.isPullback_baseChangeMap p (O := O) (k := k) toκ
  have hw : (Spec.map (CommRingCat.ofHom toκ) ≫ s) ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom toκ) := by
    rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
  let ℓ : Spec (CommRingCat.of k) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := Hsq.lift _ _ hw
  have hℓbc : ℓ ≫ (DRModel.baseChangeMap toκ) = Spec.map (CommRingCat.ofHom toκ) ≫ s := Hsq.lift_fst _ _ hw
  have hℓsnd : ℓ ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) = 𝟙 _ := Hsq.lift_snd _ _ hw
  have hbcc : (DRModel.baseChangeMap toκ).base (ℓ.base (IsLocalRing.closedPoint k)) = s.base (IsLocalRing.closedPoint O) := by
    rw [← Scheme.Hom.comp_apply, hℓbc, Scheme.Hom.comp_apply, hcl]

  have hc'' : ℓ.base (IsLocalRing.closedPoint k) ∈ Set.range (if swap then 𝔛.compZero k else 𝔛.compInf k).base := by
    rcases 𝔛.comp_jointly_surjective k (ℓ.base (IsLocalRing.closedPoint k)) with ⟨y, hy⟩ | ⟨y, hy⟩
    · cases swap
      · exact ⟨y, hy⟩
      · exact absurd ⟨y, by rw [if_pos rfl, Scheme.Hom.comp_apply, hy, hbcc]⟩ hcout
    · cases swap
      · exact absurd ⟨y, by rw [if_neg Bool.false_ne_true, Scheme.Hom.comp_apply, hy, hbcc]⟩ hcout
      · exact ⟨y, hy⟩

  have hbf : (DRModel.baseChangeMap toκ) ≫ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) := by
    simp only [DRModel.baseChangeMap, pullback.map, pullback.lift_fst, Category.comp_id]

  have hmemU : ∀ z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))), (DRModel.baseChangeMap toκ).base z ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) ↔ z ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := by
    intro z
    change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).base ((DRModel.baseChangeMap toκ).base z) ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤) ↔ (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base z ∈ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)
    rw [← Scheme.Hom.comp_apply, hbf]

  have hsec : ∀ (b : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) (z : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k))))) (hz : (DRModel.baseChangeMap toκ).base z ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))),
      (((DRModel.baseChangeMap toκ)).stalkMap z).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hz).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv b)))) =
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) z ((hmemU z).mp hz)).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv b))) := by
    intro b z hz
    rw [Scheme.Hom.germ_stalkMap_apply]
    have e1 := Scheme.Hom.congr_app hbf.symm ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)

    have e2 : ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
        (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv b)) =
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.map (eqToHom (by rw [← hbf]; rfl)).op).hom
          ((((DRModel.baseChangeMap toκ)).app ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv b)))) := by
      rw [e1]
      rfl
    rw [e2]
    symm
    erw [TopCat.Presheaf.germ_res_apply (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf]

  have hFc' : ∀ (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (hx : x ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))), x = s.base (IsLocalRing.closedPoint O) →
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) x hx).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ := by
    rintro x hx rfl; exact hFc

  have hrefl : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (y : ↥X) (g : ↥(Y.presheaf.stalk (f.base y))),
      (f.stalkMap y).hom g ∈ IsLocalRing.maximalIdeal _ → g ∈ IsLocalRing.maximalIdeal _ := by
    intro X Y f y g hg
    rw [IsLocalRing.mem_maximalIdeal] at hg ⊢
    exact fun hu => hg (hu.map _)
  have hpush : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (y : ↥X) (g : ↥(Y.presheaf.stalk (f.base y))),
      g ∈ IsLocalRing.maximalIdeal _ → (f.stalkMap y).hom g ∈ IsLocalRing.maximalIdeal _ := by
    intro X Y f y g hg
    rw [IsLocalRing.mem_maximalIdeal] at hg ⊢
    exact fun hu => hg (isUnit_of_map_unit (f.stalkMap y).hom _ hu)

  obtain ⟨C, D, hCD, hi, hii⟩ := hPKG
  obtain ⟨y₀, hy₀⟩ := hc''

  have hbad : D = (if swap then 𝔛.compZero k else 𝔛.compInf k) → False := by
    intro hD
    have hy₀D : D.base y₀ = ℓ.base (IsLocalRing.closedPoint k) := by rw [hD]; exact hy₀
    have hfin'' : (DRModel.baseChangeMap toκ).base (ℓ.base (IsLocalRing.closedPoint k)) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := hbcc ▸ hfin_c
    have hFℓ := hFc' _ hfin'' hbcc
    have hℓU : ℓ.base (IsLocalRing.closedPoint k) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := (hmemU _).mp hfin''
    have hFk : ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hℓU).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ :=
      (hsec a _ hfin'') ▸ hpush (DRModel.baseChangeMap toκ) _ _ hFℓ
    have hii' := hii y₀
    rw [hy₀D] at hii'
    obtain ⟨c₀, hc₀, hjg⟩ := hii' hℓU hFk
    have hy' : ℓ.base (IsLocalRing.closedPoint k) ∈ TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k := by
      change (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).base (ℓ.base (IsLocalRing.closedPoint k)) ∈ TwoChartIntegralModel.chartFinOpen ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
      exact (TwoChartIntegralModel.TwoChartsAux.U_eq ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ▸ hℓU
    have hjℓ := hjg hy'

    have hτ1 : ∀ c₁ : k, (Scheme.stalkClosedPointTo ℓ).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ⊤ (ℓ.base (IsLocalRing.closedPoint k)) trivial).hom
        (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c₁)) = c₁ := by
      intro c₁; exact HorSwapG.eval_const p k ℓ hℓsnd c₁
    have hτ2 : ∀ (G : Γ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))), ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))),
        (Scheme.stalkClosedPointTo (ℓ ≫ (DRModel.baseChangeMap toκ))).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hfin'').hom G) =
        toκ ((Scheme.stalkClosedPointTo s).hom (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hfin_c).hom G)) := by
      intro G; exact HorSwapG.eval_comp p O k toκ s ℓ hℓbc _ G hfin'' hfin_c

    have h0 : (Scheme.stalkClosedPointTo ℓ).hom (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) _ hy').hom
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k -
          (TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c₀))) = 0 := by
      by_contra hne
      exact (IsLocalRing.mem_maximalIdeal _).mp hjℓ (isUnit_of_map_unit (Scheme.stalkClosedPointTo ℓ).hom _ (Ne.isUnit hne))
    rw [map_sub] at h0
    have h0' : (Scheme.stalkClosedPointTo ℓ).hom (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) _ hy').hom (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) -
        (Scheme.stalkClosedPointTo ℓ).hom (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) _ hy').hom ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c₀))) = 0 := by
      rw [← map_sub]; exact h0

    have hconst : (Scheme.stalkClosedPointTo ℓ).hom (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) _ hy').hom
        ((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.map (homOfLE le_top).op (TwoChartIntegralModel.constSection ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k c₀))) = c₀ := by
      erw [TopCat.Presheaf.germ_res_apply (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf]
      exact hτ1 c₀

    have hjpart : (Scheme.stalkClosedPointTo ℓ).hom (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) _ hy').hom
        (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) =
        toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) := by

      have hj1 : (((TwoChartIntegralModel.baseChange ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k).presheaf.germ (TwoChartIntegralModel.chartFinOpenBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k) _ hy').hom
          (TwoChartIntegralModel.jCoordBC ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)) =
          ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hℓU).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) := by
        delta TwoChartIntegralModel.jCoordBC TwoChartIntegralModel.jCoord TwoChartIntegralModel.TwoChartsAux.f TwoChartIntegralModel.TwoChartsAux.sF
        have hn := Scheme.Hom.naturality (TwoChartIntegralModel.baseChangeι ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) k)
          (homOfLE (TwoChartIntegralModel.chartFinOpen_le_image_top ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))).op
        have hv := congrArg (fun φ => φ.hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
          ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))) hn
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hv
        erw [hv]
        erw [TopCat.Presheaf.germ_res_apply]
        rfl
      rw [hj1, ← hsec _ _ hfin'', ← CommRingCat.comp_apply, ← Scheme.stalkClosedPointTo_comp]
      exact hτ2 _
    rw [hconst, hjpart, sub_eq_zero] at h0'
    exact hJc (h0' ▸ hc₀)
  have hC : C = (if swap then 𝔛.compZero k else 𝔛.compInf k) := by
    by_cases hsw : swap = true
    · rw [if_pos hsw] at hbad ⊢
      exact hCD.elim (fun h => absurd h.2 hbad) (fun h => h.1)
    · rw [if_neg hsw] at hbad ⊢
      exact hCD.elim (fun h => h.1) (fun h => absurd h.2 hbad)

  have hgen : ∀ hη : (C ≫ (DRModel.baseChangeMap toκ)).base (genericPoint ↥(𝔛.ratModel k).C) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
      ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) _ hη).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ := by
    intro hη
    have hη' : (DRModel.baseChangeMap toκ).base (C.base (genericPoint ↥(𝔛.ratModel k).C)) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := hη
    have hyk : C.base (genericPoint ↥(𝔛.ratModel k).C) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ k)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) := (hmemU _).mp hη'
    have h1 := hi (genericPoint ↥(𝔛.ratModel k).C) hyk
    apply hrefl (DRModel.baseChangeMap toκ) (C.base (genericPoint ↥(𝔛.ratModel k).C))
    exact (hsec a _ hη').symm ▸ h1
  subst hC
  cases swap
  · refine ⟨fun _ => ?_, fun h => absurd h Bool.false_ne_true⟩
    simpa using hgen
  · refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    simpa using hgen

end HorAtSwap

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in

theorem HorSwapG3.strict_section_data
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ p ∣ 1)
    (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
          ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))

    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (swap : Bool)

    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base))

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) trivial).hom
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
    (a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (ha : ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq - jq ^ p) :
    ∃ (s : Spec (CommRingCat.of O) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))))
      (hs : s ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = 𝟙 _),
      s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ (DRModel.baseChangeMap toκ)).base ∧
      s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ (DRModel.baseChangeMap toκ)).base ∧
      ∃ (hfin_c : s.base (IsLocalRing.closedPoint O) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ ∧
        toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) ^ (p ^ 2) ≠
          toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨-, hePl_gal⟩ := ModularCurve.placeEquiv_unique_and_arithmeticGalois_smul_of_forall_mem_iff p ePl hePl_fun

  obtain ⟨V, hVgal, hVstrict, t, ht⟩ :=
    ModularCurve.DRResolvedModelPackage.exists_isStrictFst_forall_inertia_smul_eq_and_section_toDR_generic_eq
      p 𝔛 hA O eO k toκ 𝔛reg ePl hePl_gal P

  let s : Spec (CommRingCat.of O) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) := t.1 ≫ 𝔛reg.toDR
  have hs : s ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = 𝟙 _ := by
    simp only [s, Category.assoc, 𝔛reg.toDR_over]; exact t.2
  have hpin : Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ := by
    simpa only [s, Category.assoc] using ht

  obtain ⟨hcin, hcout⟩ := (hswap V hVgal s hs hpin).1 hVstrict

  obtain ⟨a₁, b₁, hja, hjb, hred, hne12⟩ :=
    ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst P V hVstrict
  have hjQ : ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p = ModularCurve.PlaceSpecialization.jqFun (q := p) := by
    apply Subtype.ext
    simp only [ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun, ModularCurve.PlaceSpecialization.jqFun, one_mul]
  have hjF : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p = ModularCurve.PlaceSpecialization.jFun (q := p) := rfl

  have hgrain : (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
      (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)) =
      ιK.comp (algebraMap O K) := RingHom.ext fun o => (hιK o).symm
  have htβ : Spec.map (CommRingCat.ofHom (ιK.comp (algebraMap O K))) ≫ s ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
      (𝔛.Mη.pointEquivPlace.symm (ePl V)).1 ≫ 𝔛.eη ≫
        pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) := by
    rw [← hgrain]; exact hpin
  have hφO_c : ∀ o : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (s.base (IsLocalRing.closedPoint O))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤ (s.base (IsLocalRing.closedPoint O)) trivial).hom
          (((pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of O)).inv o)))) =
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K o)) := by
    intro o
    have h1 := hφO o
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] at h1 ⊢
    exact h1

  obtain ⟨hfin_c, hβ⟩ :=
    ModularCurve.DRModelPackage.mem_preimage_and_forall_evalAt_eq_stalkClosedPointTo_of_ord_sub_pos
      p hp 𝔛 hMη O hϖO K ιK (s.base (IsLocalRing.closedPoint O)) φ hφO_c hφj P R hιA ePl hePl_fun V ⟨a₁, hja⟩
      ⟨s, hs⟩ htβ rfl
  have hβ' : ∀ s' : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk (s.base (IsLocalRing.closedPoint O)),
      φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s') ∈ V.toValuationSubring ∧
      V.evalAt (φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) s')) = ιK (algebraMap O K (Scheme.stalkClosedPointTo s s')) := by
    intro s'
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, CommRingCat.hom_id, RingHom.id_apply] using hβ s'

  have hF := HorSwapG.phi_algebraMap_germ_eq_jQFun_sub_pow p O φ hφj a ha (s.base (IsLocalRing.closedPoint O)) hfin_c
  have hJ := HorSwapG.phi_algebraMap_germ_eq_jFun p O φ hφj (s.base (IsLocalRing.closedPoint O)) hfin_c

  have hjmem : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ∈ V.toValuationSubring := by
    have h2 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a₁ : AlgebraicClosure ℚ) ∈ V.toValuationSubring :=
      V.algebraMap_mem' _
    by_cases h0 : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a₁ : AlgebraicClosure ℚ) = 0
    · rw [sub_eq_zero] at h0; rw [h0]; exact h2
    · have := V.mem_of_ord_nonneg h0 hja.le
      simpa using add_mem this h2
  have hjqmem : ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p ∈ V.toValuationSubring := by
    have h2 : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b₁ : AlgebraicClosure ℚ) ∈ V.toValuationSubring :=
      V.algebraMap_mem' _
    rw [hjQ]
    by_cases h0 : ModularCurve.PlaceSpecialization.jqFun (q := p) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b₁ : AlgebraicClosure ℚ) = 0
    · rw [sub_eq_zero] at h0; rw [h0]; exact h2
    · have := V.mem_of_ord_nonneg h0 hjb.le
      simpa using add_mem this h2
  have hevJ : V.evalAt (ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p) = (a₁ : AlgebraicClosure ℚ) := by
    rw [AlgebraicCurve.Place.evalAt_congr V hjmem (V.algebraMap_mem' (a₁ : AlgebraicClosure ℚ)) ?_, AlgebraicCurve.Place.evalAt_algebraMap]
    by_cases h0 : ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a₁ : AlgebraicClosure ℚ) = 0
    · exact Or.inl h0
    · exact Or.inr hja

  have hevF : V.evalAt (ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p) =
      ((b₁ - a₁ ^ p : ↥A) : AlgebraicClosure ℚ) := by

    set W := V.toValuationSubring with hW
    have hFmem : ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p ∈ W :=
      sub_mem hjqmem (pow_mem hjmem p)
    have hgmem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((b₁ - a₁ ^ p : ↥A) : AlgebraicClosure ℚ) ∈ W :=
      V.algebraMap_mem' _
    refine (AlgebraicCurve.Place.evalAt_congr V hFmem hgmem ?_).trans (AlgebraicCurve.Place.evalAt_algebraMap V _)

    have hunit_ord : ∀ z : ↥W, IsUnit z → V.ord (z : ↥(modularFunctionFieldBar (1 * p))) = 0 := fun z hz => V.ord_coe_unit hz.unit
    have mem_m_of_ord_pos : ∀ z : ↥W, ((z : ↥(modularFunctionFieldBar (1 * p))) = 0 ∨ 0 < V.ord (z : ↥(modularFunctionFieldBar (1 * p)))) → z ∈ IsLocalRing.maximalIdeal ↥W := by
      intro z hz
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      rcases hz with h0 | hpos
      · exact hu.ne_zero (Subtype.ext h0)
      · have := hunit_ord z hu; omega
    have ord_pos_of_mem_m : ∀ z : ↥W, z ∈ IsLocalRing.maximalIdeal ↥W → ((z : ↥(modularFunctionFieldBar (1 * p))) = 0 ∨ 0 < V.ord (z : ↥(modularFunctionFieldBar (1 * p)))) := by
      intro z hz
      by_cases h0 : (z : ↥(modularFunctionFieldBar (1 * p))) = 0
      · exact Or.inl h0
      · right
        obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥W
        obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
          (x := z) (fun h => h0 (by rw [h]; rfl)) hπ
        have hcoe : (z : ↥(modularFunctionFieldBar (1 * p))) = ((u : ↥W) : ↥(modularFunctionFieldBar (1 * p))) * ((π : ↥(modularFunctionFieldBar (1 * p))) ^ (n : ℤ)) := by
          have h := congrArg Subtype.val hu; push_cast at h; rw [zpow_natCast]; exact h
        rw [hcoe, V.ord_unit_smul_zpow u hπ (n : ℤ)]
        rcases Nat.eq_zero_or_pos n with hn | hn
        · exfalso
          rw [hn, pow_zero, mul_one] at hu
          rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hz
          exact hz (hu ▸ u.isUnit)
        · exact_mod_cast hn

    set xJ : ↥W := ⟨_, hjmem⟩ with hxJ
    set xQ : ↥W := ⟨_, hjqmem⟩ with hxQ
    set yA : ↥W := ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a₁ : AlgebraicClosure ℚ), V.algebraMap_mem' _⟩ with hyA
    set yB : ↥W := ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b₁ : AlgebraicClosure ℚ), V.algebraMap_mem' _⟩ with hyB
    have h1 : xJ - yA ∈ IsLocalRing.maximalIdeal ↥W := by
      apply mem_m_of_ord_pos
      by_cases h0 : ((xJ - yA : ↥W) : ↥(modularFunctionFieldBar (1 * p))) = 0
      · exact Or.inl h0
      · exact Or.inr hja
    have h2 : xQ - yB ∈ IsLocalRing.maximalIdeal ↥W := by
      apply mem_m_of_ord_pos
      by_cases h0 : ((xQ - yB : ↥W) : ↥(modularFunctionFieldBar (1 * p))) = 0
      · exact Or.inl h0
      · right
        have e : ((xQ - yB : ↥W) : ↥(modularFunctionFieldBar (1 * p))) =
            ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b₁ : AlgebraicClosure ℚ) := rfl
        rw [e, hjQ]; exact hjb
    have hD : (xQ - xJ ^ p) - (yB - yA ^ p) ∈ IsLocalRing.maximalIdeal ↥W := by
      obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow xJ yA p
      rw [show (xQ - xJ ^ p) - (yB - yA ^ p) = (xQ - yB) - (xJ ^ p - yA ^ p) by ring, hc]
      exact sub_mem h2 (Ideal.mul_mem_right c _ h1)
    have hD' := ord_pos_of_mem_m _ hD
    have hcoeD : (((xQ - xJ ^ p) - (yB - yA ^ p) : ↥W) : ↥(modularFunctionFieldBar (1 * p))) =
        ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p -
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((b₁ - a₁ ^ p : ↥A) : AlgebraicClosure ℚ) := by
      simp only [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, map_sub, map_pow]
      rfl
    rwa [hcoeD] at hD'

  have hFval := (hβ' ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))))).2
  rw [hF, hevF] at hFval
  have hFc : (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a)))) ∈ IsLocalRing.maximalIdeal _ := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu2 : IsUnit (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))) := hu.map _
    obtain ⟨o', ho'⟩ := hu2.exists_right_inv

    have hAunit : IsUnit (b₁ - a₁ ^ p : ↥A) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨ιK (algebraMap O K o'), hιA o'⟩, ?_⟩
      apply Subtype.ext
      show ((b₁ - a₁ ^ p : ↥A) : AlgebraicClosure ℚ) * ιK (algebraMap O K o') = 1
      rw [hFval, ← map_mul, ← map_mul, ho', map_one, map_one]
    have hred0 : red (b₁ - a₁ ^ p) = 0 := by rw [map_sub, map_pow, hred, sub_self]
    exact (hAunit.map red).ne_zero hred0

  have hJval := (hβ' ((((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))))))).2
  rw [hJ, hevJ] at hJval
  have htoκJ : toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) = red a₁ := by
    rw [htoκ]
    congr 1
    apply Subtype.ext
    show algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ) _ = (a₁ : AlgebraicClosure ℚ)
    rw [← hιK]
    exact hJval.symm
  refine ⟨s, hs, hcin, hcout, hfin_c, hFc, ?_⟩
  rw [htoκJ]
  exact hne12

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
open Classical in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime p)
    (𝔛 : DRModelPackage p)

    [hneη : Nonempty (Scheme.Opens.toScheme
      ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)))]
    (hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)),
      ((𝔛.Mη.ffEquiv.symm
          (𝔛.Mη.C.germToFunctionField
            ((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤))
            (((𝔛.eη ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))).app
                ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of
                  ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))))
          : ↥(modularFunctionFieldBar p)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ))

    (ePl : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ≃ Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar p))
    (hePl_fun : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)))
        (f : ↥(modularFunctionFieldBar (1 * p))) (f' : ↥(modularFunctionFieldBar p)),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = (f' : LaurentSeries (AlgebraicClosure ℚ)) →
        (f ∈ V.toValuationSubring ↔ f' ∈ (ePl V).toValuationSubring) ∧ V.evalAt f = (ePl V).evalAt f')

    {k : Type} [Field k] [CharP k p] [PerfectField k] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (R : ProlongationTuple P) [DecidableEq k] (hqN : ¬ p ∣ 1)
    (hR : R.IsModel)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces p 1 k)
    (hreg : R.RegularityLaw W) (hval : R.NodeValueLaw W)
    (e : Place k (modularFunctionFieldC k 1) → ℕ) (he : ∀ w ∈ W, 1 ≤ e w)
    (hVI : ∀ w ∈ W, R.ValueIntegralityLaw w)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (eO : O ≃+* ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))))
    (hϖO : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (ιK : K →+* AlgebraicClosure ℚ)
    (hιK : ∀ o : O, ιK (algebraMap O K o) =
      algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
        ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
          ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))))

    (hιA : ∀ a : O, ιK (algebraMap O K a) ∈ A)
    (toκ : O →+* k)
    (htoκ : ∀ o : O, toκ o = red ⟨algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)
      ((eO o : ↥(A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)))) :
        ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ))), (eO o).2⟩)

    (𝔛reg : DRResolvedModelPackage p 𝔛 O k toκ)
    (σN : ↥W ≃ 𝔛reg.node) (hσN : ∀ w : ↥W, 𝔛reg.width (σN w) = e (w : Place k (modularFunctionFieldC k 1)))
    (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W) (swap : Bool)

    (hswap : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        (P.IsStrictFst V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base) ∧
        (P.IsStrictSnd V →
          s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ DRModel.baseChangeMap toκ).base ∧
          s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ DRModel.baseChangeMap toκ).base))

    [hint : IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (φ : ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) →+*
      ↥(modularFunctionFieldBar (1 * p)))

    (hφO : ∀ a : O,
      φ (algebraMap ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) _
        (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ⊤
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))) trivial).hom
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

    (hnodePt : ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hw : P.reduceFst V ∈ W),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * p)) σ • V = V) →
      ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V →
      ∀ s : Spec (CommRingCat.of O) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))),
        s ≫ pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) = 𝟙 _ →
        Spec.map (CommRingCat.ofHom ((algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ)).comp
            (((A.comap (algebraMap ↥(IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)) (AlgebraicClosure ℚ))).subtype.comp eO.toRingHom)))) ≫ s ≫ pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) =
          ((𝔛.Mη.pointEquivPlace).symm (ePl V)).1 ≫ 𝔛.eη ≫ pullback.fst (DRModel.toBase p) _ →
        s.base (IsLocalRing.closedPoint O) =
          (pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨P.reduceFst V, hw⟩)))

    (hxj : ∃ ĵ : O, red ⟨ιK (algebraMap O K ĵ), hιA ĵ⟩ = w.evalAt (jGeomGen k 1) ∧
      ∃ t ∈ IsLocalRing.maximalIdeal ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk
          ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))),
        φ (algebraMap _ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField t) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p -
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (ιK (algebraMap O K ĵ)))

    (hspInf : ((𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))))
    (hspZero : ((𝔛.compZero k ≫ DRModel.baseChangeMap toκ).base (genericPoint ↥(𝔛.ratModel k).C)) ⤳ ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩)))) :
    (swap = false →
      ∃ tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))),
        φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) tF) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p ∧
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspInf).hom tF ∈ IsLocalRing.maximalIdeal _) ∧
    (swap = true →
      ∃ tF : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalk ((pullback.fst (𝔛.compInf k) (𝔛.compZero k) ≫ 𝔛.compInf k ≫ DRModel.baseChangeMap toκ).base (𝔛reg.nodeEquiv (σN ⟨w, hw⟩))),
        φ (algebraMap _ ↥((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).functionField) tF) =
          ModularCurve.PlaceSpecialization.ProlongationTuple.jQFun 1 p - ModularCurve.PlaceSpecialization.ProlongationTuple.jFun 1 p ^ p ∧
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.stalkSpecializes hspZero).hom tF ∈ IsLocalRing.maximalIdeal _) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have hker : RingHom.ker toκ = IsLocalRing.maximalIdeal O := by
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top toκ)
    · rw [hϖO, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_natCast]
      exact CharP.cast_eq_zero k p

  obtain ⟨a, ha⟩ := HorSwapG.exists_chartAlgFin_coe_eq_qExpand_sub_pow p
  have hfinw := HorSwapG.node_mem_preimage_chartFin p hp 𝔛 O k toκ 𝔛reg (σN ⟨w, hw⟩)

  have htF := HorSwapG.phi_algebraMap_germ_eq_jQFun_sub_pow p O φ hφj a ha _ hfinw

  have G3 : ∃ (s : Spec (CommRingCat.of O) ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))) (hs : s ≫ (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) = 𝟙 _),
      s.base (IsLocalRing.closedPoint O) ∈ Set.range ((if swap then 𝔛.compZero k else 𝔛.compInf k) ≫ (DRModel.baseChangeMap toκ)).base ∧
      s.base (IsLocalRing.closedPoint O) ∉ Set.range ((if swap then 𝔛.compInf k else 𝔛.compZero k) ≫ (DRModel.baseChangeMap toκ)).base ∧
      ∃ hfin_c : s.base (IsLocalRing.closedPoint O) ∈ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)),
        ((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv a))) ∈ IsLocalRing.maximalIdeal _ ∧
        toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) ^ (p ^ 2) ≠
          toκ (Scheme.stalkClosedPointTo s (((pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).presheaf.germ ((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)) (s.base (IsLocalRing.closedPoint O)) hfin_c).hom (((pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).app ((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) ''ᵁ ⊤)).hom (((TwoChartIntegralModel.ιFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))).inv (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))))))) := by
    exact HorSwapG3.strict_section_data p hp hA 𝔛 hMη ePl hePl_fun P R hqN hR W hW hreg hval e he hVI O eO hϖO K ιK hιK hιA toκ htoκ 𝔛reg σN hσN w hw swap hswap φ hφO hφj a ha
  obtain ⟨s, hs, hcin, hcout, hfin_c, hFc, hJc⟩ := G3
  have hPKG := ModularCurve.DRModelPackage.exists_range_comp_subset_zeroLocus_jq_sub_pow p hp 𝔛 k a ha
  have M := HorAtSwap.main p hp 𝔛 O k toκ hker a hPKG swap s hs hcin hcout hfin_c hFc hJc
  refine ⟨fun h => ⟨_, htF, ?_⟩, fun h => ⟨_, htF, ?_⟩⟩
  · rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    exact M.1 h _
  · rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
    exact M.2 h _

end S_ModularCurve_DRModelPackage_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap (solution)
