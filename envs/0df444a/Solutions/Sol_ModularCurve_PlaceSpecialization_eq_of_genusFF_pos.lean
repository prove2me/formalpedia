-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.eq_of_genusFF_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1135c36a-727e-5d36-8181-52fe5b5fb7ef

import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_exists_finset_place_eq_of_ord_jqModC_sub_pos
import Theorems.Thm_ModularCurve_ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_eq_of_sp_eq
import Theorems.Thm_ModularCurve_constantsAreBase_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_eq_of_genusFF_pos
p2m_attr_erase "instance" "CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne"
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen"
p2m_attr_erase "simp" "ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
open AlgebraicCurve

section FG

private theorem t2_fst_eq_zero {n : ℕ} (c : Fin n →₀ ℤ)
    (h : ∀ m : ℕ, m ≠ 0 → ∃ d : Fin n →₀ ℤ, m • d = c) : c = 0 := by
  ext i
  set m : ℕ := (c i).natAbs + 1 with hm
  obtain ⟨d, hd⟩ := h m (Nat.succ_ne_zero _)
  have hc : c i = m • d i := by
    rw [← hd]
    exact map_nsmul (Finsupp.applyAddHom i) m d
  have hdvd : (m : ℤ) ∣ c i := ⟨d i, by rw [hc, nsmul_eq_mul]⟩
  refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
  rw [Int.abs_eq_natAbs, hm]
  push_cast
  omega

private theorem t2_eq_zero_of_forall_nsmul {Q : Type*} [AddCommGroup Q] [AddGroup.FG Q] (x : Q)
    (hx : ∀ m : ℕ, m ≠ 0 → ∃ y : Q, m • y = x) : x = 0 := by
  obtain ⟨n, ι, hι, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod Q
  haveI : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  haveI : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_injective (fun t : DirectSum ι fun i => ZMod (p i ^ e i) => (t : ∀ i, ZMod (p i ^ e i)))
      DFunLike.coe_injective
  rw [← f.map_eq_zero_iff]
  refine Prod.ext ?_ ?_
  · refine t2_fst_eq_zero (f x).1 fun m hm => ?_
    obtain ⟨y, hy⟩ := hx m hm
    exact ⟨(f y).1, by rw [← hy, map_nsmul]; rfl⟩
  · obtain ⟨y, hy⟩ := hx (Nat.card (DirectSum ι fun i => ZMod (p i ^ e i))) Nat.card_pos.ne'
    have h2 : (f x).2 = Nat.card (DirectSum ι fun i => ZMod (p i ^ e i)) • (f y).2 := by
      rw [← hy, map_nsmul]; rfl
    rw [h2, card_nsmul_eq_zero']
    rfl

private theorem t2_fg_finsupp (β : Type*) [Finite β] : AddGroup.FG (β →₀ ℤ) :=
  Module.Finite.iff_addGroup_fg.mp inferInstance

private theorem t2_fg_finsupp' (β : Type*) [Finite β] : AddGroup.FG (β →₀ ℤ) := by
  classical
  refine AddGroup.fg_iff.mpr ⟨Set.range fun b : β => Finsupp.single b (1 : ℤ), ?_, Set.finite_range _⟩
  refine top_le_iff.mp fun x hx => ?_
  clear hx
  induction x using Finsupp.induction_linear with
  | zero => exact zero_mem _
  | add f g hf hg => exact add_mem hf hg
  | single b n =>
    have : Finsupp.single b n = n • Finsupp.single b (1 : ℤ) := by
      ext c
      simp [Finsupp.single_apply]
    rw [this]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self b)) n

private theorem t2_mem_of_forall_nsmul {G : Type*} [AddCommGroup G] [AddGroup.FG G] (K : AddSubgroup G)
    (x : G) (hx : ∀ m : ℕ, m ≠ 0 → ∃ e : G, ∃ z ∈ K, x = m • e + z) : x ∈ K := by
  haveI : AddGroup.FG (G ⧸ K) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective K)
  have h0 : (x : G ⧸ K) = 0 := by
    refine t2_eq_zero_of_forall_nsmul (x : G ⧸ K) fun m hm => ?_
    obtain ⟨e, z, hz, hxe⟩ := hx m hm
    refine ⟨(e : G ⧸ K), ?_⟩
    rw [hxe, QuotientAddGroup.mk_add, QuotientAddGroup.mk_nsmul, (QuotientAddGroup.eq_zero_iff z).mpr hz,
      add_zero]
  exact (QuotientAddGroup.eq_zero_iff x).mp h0

end FG

section Fibre

open ModularCurve

variable {K : Type*} [Field K] (N : ℕ) [NeZero N]

private noncomputable abbrev t2_jC : modularFunctionFieldC K N := ⟨jqModC K, jqModC_mem K N⟩

private theorem t2_jC_ne_algebraMap (a : K) : t2_jC N ≠ algebraMap K (modularFunctionFieldC K N) a := by
  intro h
  have h' : jqModC K = algebraMap K (LaurentSeries K) a := by
    have h1 := congrArg Subtype.val h
    simpa using h1
  apply ModularCurve.transcendental_jqModC K
  rw [h']
  exact isAlgebraic_algebraMap a

private theorem t2_ord_algebraMap (v : Place K (modularFunctionFieldC K N)) {a : K} (ha : a ≠ 0) :
    v.ord (algebraMap K (modularFunctionFieldC K N) a) = 0 := by
  have hne : algebraMap K (modularFunctionFieldC K N) a ≠ 0 := (map_ne_zero _).mpr ha
  have h1 := v.adicValuation_le_one_iff.mp (v.adicValuation_algebraMap_le_one a)
  have h2 := v.adicValuation_le_one_iff.mp (v.adicValuation_algebraMap_le_one a⁻¹)
  rw [map_inv₀, v.ord_inv, inv_eq_zero] at h2
  rcases h1 with h1 | h1
  · exact absurd h1 hne
  rcases h2 with h2 | h2
  · exact absurd h2 hne
  omega

private theorem t2_exists_zero [IsAlgClosed K] (c : K) :
    ∃ z : Place K (modularFunctionFieldC K N),
      0 < z.ord (t2_jC N - algebraMap K (modularFunctionFieldC K N) c) := by
  have hC : LSpace (0 : Divisor K (modularFunctionFieldC K N))
      = LinearMap.range (Algebra.linearMap K (modularFunctionFieldC K N)) :=
    ModularCurve.constantsAreBase_modularFunctionFieldC_of_perfectField K N
  set x : modularFunctionFieldC K N := t2_jC N - algebraMap K (modularFunctionFieldC K N) c with hx
  have hx0 : x ≠ 0 := sub_ne_zero.mpr (t2_jC_ne_algebraMap N c)
  by_contra hno
  have hno' : ∀ v : Place K (modularFunctionFieldC K N), v.ord x ≤ 0 := fun v =>
    not_lt.mp fun hv => hno ⟨v, hv⟩
  have hmem : x⁻¹ ∈ LSpace (0 : Divisor K (modularFunctionFieldC K N)) := by
    rw [mem_lSpace_iff_ord]
    right
    intro v
    rw [v.ord_inv, Finsupp.zero_apply, neg_zero, neg_nonneg]
    exact hno' v
  rw [hC] at hmem
  obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hmem
  have ha' : algebraMap K (modularFunctionFieldC K N) a = x⁻¹ := ha
  have hxa : x = algebraMap K (modularFunctionFieldC K N) a⁻¹ := by
    rw [map_inv₀, ha', inv_inv]
  apply t2_jC_ne_algebraMap N (a⁻¹ + c)
  have hj : t2_jC N = x + algebraMap K (modularFunctionFieldC K N) c := by
    rw [hx]; ring
  rw [hj, hxa, map_add]

private theorem t2_zero_injective {c c' : K} (z : Place K (modularFunctionFieldC K N))
    (hc : 0 < z.ord (t2_jC N - algebraMap K (modularFunctionFieldC K N) c))
    (hc' : 0 < z.ord (t2_jC N - algebraMap K (modularFunctionFieldC K N) c')) : c = c' := by
  by_contra hne
  have hsub : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have hdiff : (t2_jC N - algebraMap K (modularFunctionFieldC K N) c')
      - (t2_jC N - algebraMap K (modularFunctionFieldC K N) c)
      = algebraMap K (modularFunctionFieldC K N) (c - c') := by
    rw [map_sub]; ring
  have hv : z.adicValuation ((t2_jC N - algebraMap K (modularFunctionFieldC K N) c')
      - (t2_jC N - algebraMap K (modularFunctionFieldC K N) c)) ≤ WithZero.exp (-1 : ℤ) := by
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · exact z.adicValuation_le_exp_iff.mpr (Or.inr (by omega))
    · exact z.adicValuation_le_exp_iff.mpr (Or.inr (by omega))
  rw [hdiff] at hv
  rcases z.adicValuation_le_exp_iff.mp hv with h0 | h0
  · exact (map_ne_zero _).mpr hsub h0
  · rw [t2_ord_algebraMap N z hsub] at h0
    omega

private theorem t2_exists_place_notMem [IsAlgClosed K] (B : Finset (Place K (modularFunctionFieldC K N))) :
    ∃ v : Place K (modularFunctionFieldC K N), v ∉ B := by
  choose z hz using t2_exists_zero (K := K) N
  have hinj : Function.Injective z := fun c c' h =>
    t2_zero_injective N (z c) (hz c) (by rw [h]; exact hz c')
  haveI : Infinite (Place K (modularFunctionFieldC K N)) := Infinite.of_injective z hinj
  exact Infinite.exists_notMem_finset B

end Fibre

section Genus

open ModularCurve

variable {K : Type*} [Field K] [IsAlgClosed K] (q : ℕ) [CharP K q] (N : ℕ) [NeZero N]

private theorem t2_ell_eq (hqN : ¬ q ∣ N) (D : Divisor K (modularFunctionFieldC K N))
    (hD : 2 * (genusFF K (modularFunctionFieldC K N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF K (modularFunctionFieldC K N) : ℤ) := by
  have h := ModularCurve.modularFunctionFieldC_eq_modularFunctionFieldFullC K q N hqN
  revert D
  rw [h]
  intro D hD
  exact ModularCurve.ell_eq_degree_add_one_sub_genusFF_modularFunctionFieldFullC K N D hD

private theorem t2_transcendental_of_ord_eq_one {f : modularFunctionFieldC K N}
    (v : Place K (modularFunctionFieldC K N)) (hv : v.ord f = 1) : Transcendental K f := by
  intro halg
  have hint : IsIntegral K f := isAlgebraic_iff_isIntegral.mp halg
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at hv
    exact zero_ne_one hv
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact hf0 ha.symm
  rw [← ha, t2_ord_algebraMap N v ha0] at hv
  exact zero_ne_one hv

omit [IsAlgClosed K] in
private theorem t2_linearIndependent_pow {f : modularFunctionFieldC K N} (hf : Transcendental K f) :
    LinearIndependent K fun i : ℕ => f ^ i := by
  have hker : LinearMap.ker (Polynomial.aeval f).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun p hp => by
      by_contra hp0
      exact hf ⟨p, hp0, hp⟩
  have h := (Polynomial.basisMonomials K).linearIndependent.map' (Polynomial.aeval f).toLinearMap hker
  convert h using 1 <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _
  funext i
  simp [Polynomial.coe_basisMonomials]

private theorem t2_eq_of_isPrincipal (hqN : ¬ q ∣ N) (hg : 0 < genusFF K (modularFunctionFieldC K N))
    {b b' : Place K (modularFunctionFieldC K N)}
    (h : Divisor.IsPrincipal (Finsupp.single b' (1 : ℤ) - Finsupp.single b (1 : ℤ))) : b' = b := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := h
  set g : ℕ := genusFF K (modularFunctionFieldC K N) with hgdef

  have hbb' : ¬ b = b' := fun h => hne h.symm
  have hord_b : b.ord f = -1 := by
    have := hf b
    simp [hne] at this
    omega
  have hord_b' : b'.ord f = 1 := by
    have := hf b'
    simp [hbb'] at this
    omega
  have hord_other : ∀ v, v ≠ b → 0 ≤ v.ord f := by
    intro v hv
    have := hf v
    simp only [Finsupp.sub_apply, Finsupp.single_apply, if_neg (show ¬ b = v from fun h => hv h.symm)] at this
    split_ifs at this <;> omega

  set D : Divisor K (modularFunctionFieldC K N) := Finsupp.single b (2 * g : ℤ) with hDdef
  have hdegD : Divisor.degree D = 2 * g := by
    rw [hDdef, Divisor.degree_single, ModularCurve.place_deg_eq_one_of_isAlgClosed K N b]
    simp
  have hell : (ell D : ℤ) = g + 1 := by
    rw [t2_ell_eq q N hqN D (by rw [hdegD]; omega), hdegD]
    ring

  have hmem : ∀ i : Fin (2 * g + 1), f ^ (i : ℕ) ∈ LSpace D := by
    intro i
    rw [mem_lSpace_iff_ord]
    right
    intro v
    have hpow : v.ord (f ^ (i : ℕ)) = (i : ℕ) * v.ord f := by
      have := v.ord_zpow f (i : ℕ)
      rw [zpow_natCast] at this
      exact this
    rw [hpow, hDdef, Finsupp.single_apply]
    split_ifs with hbv
    · subst hbv
      rw [hord_b]
      have := i.isLt
      omega
    · have := hord_other v (Ne.symm hbv)
      rw [neg_zero]
      exact mul_nonneg (Nat.cast_nonneg _) this
  have hli : LinearIndependent K fun i : Fin (2 * g + 1) => (⟨f ^ (i : ℕ), hmem i⟩ : LSpace D) := by
    have h0 := t2_linearIndependent_pow N (t2_transcendental_of_ord_eq_one N b' hord_b')
    have h1 : LinearIndependent K fun i : Fin (2 * g + 1) => f ^ (i : ℕ) :=
      h0.comp (fun i : Fin (2 * g + 1) => (i : ℕ)) Fin.val_injective
    exact LinearIndependent.of_comp (LSpace D).subtype h1
  haveI : Module.Finite K (LSpace D) := Module.finite_of_finrank_pos (by
    have : (0 : ℤ) < ell D := by rw [hell]; omega
    exact_mod_cast this)
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  have hell' : Module.finrank K (LSpace D) = g + 1 := by exact_mod_cast hell
  rw [hell'] at hcard
  omega

end Genus

section Packets

open ModularCurve ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data} {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private structure t2_Collisions (k : Type*) [Field k] (N : ℕ) [NeZero N] where
  B : Finset (Place k (modularFunctionFieldC k N))
  pole_j : ∀ Q : Place k (modularFunctionFieldC k N),
    Q.ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 → Q ∈ B
  pole_jN : ∀ Q : Place k (modularFunctionFieldC k N),
    Q.ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) < 0 → Q ∈ B
  det : ∀ Q : Place k (modularFunctionFieldC k N), Q ∉ B →
    ∀ (Q' : Place k (modularFunctionFieldC k N)) (s t : k),
      0 < Q.ord (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) s) →
      0 < Q.ord (⟨jqNModC k N, jqNModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) t) →
      0 < Q'.ord (⟨jqModC k, jqModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) s) →
      0 < Q'.ord (⟨jqNModC k N, jqNModC_mem k N⟩ - algebraMap k (modularFunctionFieldC k N) t) →
      Q' = Q

private theorem t2_collisions [IsAlgClosed k] (hqN : ¬ q ∣ N) : Nonempty (t2_Collisions k N) := by
  obtain ⟨B, h1, h2, h3⟩ := exists_finset_place_eq_of_ord_jqModC_sub_pos k q N hqN
  exact ⟨⟨B, h1, h2, h3⟩⟩

private theorem t2_sp_eq_of_notMem (C : t2_Collisions k N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hw : P.sp w ∉ C.B) :
    P'.sp w = P.sp w := by

  have hj : ¬ (P.sp w).ord (⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N) < 0 :=
    fun h => hw (C.pole_j _ h)
  obtain ⟨a, ha⟩ := not_forall.mp (mt (P.d0_j_pole w) hj)
  have ha' := not_le.mp ha

  have hjN : ¬ (P.sp w).ord (⟨jqNModC k N, jqNModC_mem k N⟩ : modularFunctionFieldC k N) < 0 :=
    fun h => hw (C.pole_jN _ h)
  obtain ⟨a', ha₁⟩ := not_forall.mp (mt (P.d0_jN_pole w) hjN)
  have ha₁' := not_le.mp ha₁
  exact C.det (P.sp w) hw (P'.sp w) (red a) (red a') (P.d0_j w a ha') (P.d0_jN w a' ha₁')
    (P'.d0_j w a ha') (P'.d0_jN w a' ha₁')

open scoped Classical in

private noncomputable def t2_disc (C : t2_Collisions k N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : (C.B →₀ ℤ) :=
  if h : P.sp w ∈ C.B ∧ P'.sp w ∈ C.B then
    Finsupp.single ⟨P'.sp w, h.2⟩ 1 - Finsupp.single ⟨P.sp w, h.1⟩ 1
  else 0

private noncomputable def t2_Disc (C : t2_Collisions k N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →+ (C.B →₀ ℤ) :=
  Finsupp.liftAddHom fun w => zmultiplesHom _ (t2_disc C P P' w)

private noncomputable def t2_incl (C : t2_Collisions k N) :
    (C.B →₀ ℤ) →+ Divisor k (modularFunctionFieldC k N) :=
  Finsupp.mapDomain.addMonoidHom (fun b : C.B => (b : Place k (modularFunctionFieldC k N)))

private noncomputable def t2_Push (P P' : PlaceSpecialization A q N data hKr k red hα hβ) :
    Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →+ Divisor k (modularFunctionFieldC k N) :=
  Finsupp.mapDomain.addMonoidHom P'.sp - Finsupp.mapDomain.addMonoidHom P.sp

private theorem t2_Push_single (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (n : ℤ) :
    t2_Push P P' (Finsupp.single w n) = Finsupp.single (P'.sp w) n - Finsupp.single (P.sp w) n := by
  simp [t2_Push, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]

private theorem t2_incl_disc (C : t2_Collisions k N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    t2_incl C (t2_disc C P' P w) = Finsupp.single (P.sp w) 1 - Finsupp.single (P'.sp w) 1 := by
  unfold t2_disc
  split_ifs with h
  · rw [map_sub]
    simp [t2_incl, Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
  · rw [map_zero]
    have heq : P.sp w = P'.sp w := by
      rcases not_and_or.mp h with h1 | h1
      · exact t2_sp_eq_of_notMem C P' P w h1
      · exact (t2_sp_eq_of_notMem C P P' w h1).symm
    rw [heq, sub_self]

private theorem t2_incl_comp_Disc (C : t2_Collisions k N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ) :
    (t2_incl C).comp (t2_Disc C P' P) = t2_Push P' P := by
  refine Finsupp.addHom_ext fun w n => ?_
  rw [AddMonoidHom.comp_apply, t2_Disc, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply,
    map_zsmul, t2_incl_disc, t2_Push_single]
  classical
  ext c
  by_cases h1 : P.sp w = c <;> by_cases h2 : P'.sp w = c <;> simp [h1, h2]

private theorem t2_Push_principal (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)} (hD : Divisor.IsPrincipal D) :
    t2_Push P P' D ∈ Divisor.principal := by
  obtain ⟨f, hf0, hf⟩ := hD
  have h1 : Finsupp.mapDomain P'.sp D ∈ Divisor.principal (K := k) (F := modularFunctionFieldC k N) :=
    P'.d5 f hf0 D hf
  have h2 : Finsupp.mapDomain P.sp D ∈ Divisor.principal (K := k) (F := modularFunctionFieldC k N) :=
    P.d5 f hf0 D hf
  have : t2_Push P P' D = Finsupp.mapDomain P'.sp D - Finsupp.mapDomain P.sp D := by
    simp [t2_Push, Finsupp.mapDomain.addMonoidHom_apply]
  rw [this]
  exact Divisor.principal.sub_mem h1 h2

private theorem t2_exists_nsmul_add_principal
    (w w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (m : ℕ) (hm : m ≠ 0) :
    ∃ E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ D₀ ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N),
        Finsupp.single w (1 : ℤ) - Finsupp.single w₀ (1 : ℤ) = m • E + D₀ := by
  have hdeg : Finsupp.single w (1 : ℤ) - Finsupp.single w₀ (1 : ℤ)
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) := by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      deg_eq_one_modularFunctionFieldBar N w, deg_eq_one_modularFunctionFieldBar N w₀, sub_self]
  set x : JZero N := Pic0.mk ⟨_, hdeg⟩ with hxdef
  obtain ⟨y, hy⟩ := JZero.divisible N m hm x
  obtain ⟨E', rfl⟩ := Pic0.mk_surjective y
  have hmk : (m • Pic0.mk E' : JZero N) = Pic0.mk (m • E') := rfl
  rw [hmk, hxdef] at hy

  have hmem : m • E' - (⟨_, hdeg⟩ : Divisor.degZero) ∈ (Divisor.principal (K := AlgebraicClosure ℚ)
      (F := modularFunctionFieldBar N)).addSubgroupOf Divisor.degZero :=
    QuotientAddGroup.eq_iff_sub_mem.mp hy
  have hmem' : ((m • E' - (⟨_, hdeg⟩ : Divisor.degZero) : Divisor.degZero)
      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) ∈ Divisor.principal :=
    AddSubgroup.mem_addSubgroupOf.mp hmem
  have hval : ((m • E' - (⟨_, hdeg⟩ : Divisor.degZero) : Divisor.degZero)
      : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = m • (E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        - (Finsupp.single w (1 : ℤ) - Finsupp.single w₀ (1 : ℤ)) := rfl
  rw [hval] at hmem'
  refine ⟨(E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), _,
    Divisor.principal.neg_mem hmem', ?_⟩
  abel

private theorem t2_push_single_principal [IsAlgClosed k] (C : t2_Collisions k N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Divisor.IsPrincipal (Finsupp.single (P.sp w) (1 : ℤ) - Finsupp.single (P'.sp w) (1 : ℤ)) := by

  obtain ⟨v₀, hv₀⟩ := t2_exists_place_notMem N C.B
  obtain ⟨w₀, hw₀⟩ := P'.d4 v₀
  have hw₀B : P'.sp w₀ ∉ C.B := hw₀ ▸ hv₀
  have hdisc₀ : t2_disc C P' P w₀ = 0 := by
    unfold t2_disc
    exact dif_neg fun h => hw₀B h.1

  haveI : AddGroup.FG (C.B →₀ ℤ) := t2_fg_finsupp C.B
  set Kpr : AddSubgroup (C.B →₀ ℤ) :=
    (Divisor.principal (K := k) (F := modularFunctionFieldC k N)).comap (t2_incl C) with hKpr
  have hx : t2_disc C P' P w ∈ Kpr := by
    refine t2_mem_of_forall_nsmul Kpr _ fun m hm => ?_
    obtain ⟨E, D₀, hD₀, hE⟩ := t2_exists_nsmul_add_principal w w₀ m hm
    refine ⟨t2_Disc C P' P E, t2_Disc C P' P D₀, ?_, ?_⟩
    · rw [hKpr, AddSubgroup.mem_comap, ← AddMonoidHom.comp_apply, t2_incl_comp_Disc]
      exact t2_Push_principal P' P hD₀
    · have h1 := congrArg (t2_Disc C P' P) hE
      rw [map_sub, map_add, map_nsmul] at h1
      have h2 : ∀ u, t2_Disc C P' P (Finsupp.single u (1 : ℤ)) = t2_disc C P' P u := by
        intro u
        rw [t2_Disc, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]
      rw [h2, h2, hdisc₀, sub_zero] at h1
      exact h1
  rw [hKpr, AddSubgroup.mem_comap, t2_incl_disc] at hx
  exact hx

private theorem t2_sp_eq [IsAlgClosed k] (hg : 0 < genusFF k (modularFunctionFieldC k N)) (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ) : P.sp = P'.sp := by
  obtain ⟨C⟩ := t2_collisions (k := k) (N := N) hqN
  funext w
  exact t2_eq_of_isPrincipal q N hqN hg (t2_push_single_principal C P P' w)

end Packets

open ModularCurve ModularCurve.PlaceSpecialization in
theorem solution {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k]
    (hg : 0 < genusFF k ↥(modularFunctionFieldC k N)) (hqN : ¬ q ∣ N)
    (P P' : PlaceSpecialization A q N data hKr k red hα hβ) : P = P' := by
  have hsp : P.sp = P'.sp := t2_sp_eq hg hqN P P'
  have hpic : P.spPic0 = P'.spPic0 := PlaceSpecialization.spPic0_eq_of_sp_eq P P' hsp
  obtain ⟨sp, pic, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := P
  obtain ⟨sp', pic', _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := P'
  change sp = sp' at hsp
  change pic = pic' at hpic
  subst hsp hpic
  rfl

end S_ModularCurve_PlaceSpecialization_eq_of_genusFF_pos
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_eq_of_genusFF_pos (solution)
