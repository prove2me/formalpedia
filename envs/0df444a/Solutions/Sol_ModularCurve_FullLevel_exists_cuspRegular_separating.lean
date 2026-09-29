-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_cuspRegular_separating
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/c0af8231-ae4f-5670-a6d1-66351f5025e5

import Mathlib
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero
import Theorems.Thm_ModularCurve_FullLevel_exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_cuspRegular_separating
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.cuspCount_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

namespace SepGlue

section Transport
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
theorem transport_of_eq {E₁ E₂ : IntermediateField K L} (h : E₁ = E₂) :
    (IsCurveOver K ↥E₂ → IsCurveOver K ↥E₁) ∧
    (Algebra.EssFiniteType K ↥E₂ → Algebra.EssFiniteType K ↥E₁) := by
  subst h; exact ⟨id, id⟩
end Transport

section Constants
variable (k F : Type*) [Field k] [IsAlgClosed k] [Field F] [Algebra k F] [IsCurveOver k F] [Algebra.EssFiniteType k F]

theorem exists_eq_algebraMap_of_forall_ord_nonneg (f : F) (hf : ∀ v : Place k F, 0 ≤ v.ord f) :
    ∃ c : k, f = algebraMap k F c := by
  obtain ⟨t, ht, hfin, -⟩ := AlgebraicCurve.IsCurveOver.exists_separating_transcendental (K := k) (F := F)
  obtain ⟨hfd, hell⟩ :=
    AlgebraicCurve.finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental k t ht hfin
  haveI := hfd
  have h1 : (1 : F) ∈ LSpace (0 : Divisor k F) := by
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    simp
  have hfmem : f ∈ LSpace (0 : Divisor k F) := by
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    simpa using hf v
  have hne : (⟨1, h1⟩ : ↥(LSpace (0 : Divisor k F))) ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨1, h1⟩ : ↥(LSpace (0 : Divisor k F))) hne).mp hell ⟨f, hfmem⟩
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simp only [SetLike.val_smul] at this
  rw [← this, Algebra.smul_def, mul_one]

end Constants

section MapDomain
variable {α β : Type*} (r : α → β)

theorem mapDomain_apply_nonneg_of_forall (D : α →₀ ℤ) (Q : β)
    (h : ∀ P, r P = Q → D P < 0 → False) : 0 ≤ Finsupp.mapDomain r D Q := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_nonneg fun a _ => ?_
  show (0 : ℤ) ≤ (Finsupp.single (r a) (D a)) Q
  rw [Finsupp.single_apply]
  split_ifs with hra
  · by_contra hlt
    exact h a hra (lt_of_not_ge hlt)
  · exact le_rfl

end MapDomain

end SepGlue

open SepGlue

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A)) :
    ∀ s s' : ↥W, s ≠ s' → ∃ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
      (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
        0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) ∧
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
          (s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring ∧
      (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) ≠
        (s' : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt (R₀.residue ⟨f, hf⟩) := by
  classical
  intro s s' hss'

  haveI hκac : IsAlgClosed (ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField_of_isAlgClosed A
  haveI hκch : CharP (ResidueField ↥A) q := ValuationSubring.residueField_charP_of_liesOverPrime A (Fact.out : q.Prime) hA
  have heqF : modularFunctionFieldC (ResidueField ↥A) M' = modularFunctionFieldFullC (ResidueField ↥A) M' :=
    modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField ↥A) q M' hqM'
  obtain ⟨hIC, hEF⟩ := transport_of_eq (K := (ResidueField ↥A)) heqF
  haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := hIC (isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) M')
  haveI : Algebra.EssFiniteType (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') := hEF (essFiniteType_modularFunctionFieldFullC (ResidueField ↥A) M')
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M') := isCurveOver_modularFunctionFieldBar M'

  have hcoeff : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    ext k
    rw [coeffMap_coeff, coeffEmb_coeff, ← jqModC_rat, jqModC_eq_map_intCast ↥A, jqModC_eq_map_intCast ℚ,
      HahnSeries.map_coeff, HahnSeries.map_coeff]
    simp
  have hjmem : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar M' := by
    rw [hcoeff]; exact coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))
  obtain ⟨hjO', hjres'⟩ := hR₀ (jqModC ↥A) hjmem
  have hjeq : ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) = ⟨coeffMap A.subtype (jqModC ↥A), hjmem⟩ := Subtype.ext hcoeff.symm
  have hjO : ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) ∈ R₀.integers := by rw [hjeq]; exact hjO'
  have hjres : R₀.residue ⟨((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')), hjO⟩ = jGeomGen (ResidueField ↥A) M' := by
    have h1 : R₀.residue ⟨((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')), hjO⟩ = R₀.residue ⟨_, hjO'⟩ := by congr 1; exact Subtype.ext hjeq
    rw [h1]
    apply Subtype.ext
    rw [hjres', coe_jGeomGen, jqModC_eq_map_intCast (ResidueField ↥A), jqModC_eq_map_intCast ↥A]
    ext k
    rw [coeffMap_coeff, HahnSeries.map_coeff, HahnSeries.map_coeff]
    simp
  have hjbar0 : jGeomGen (ResidueField ↥A) M' ≠ 0 := by
    have := jGeomGen_sub_algebraMap_ne_zero (ResidueField ↥A) M' 0
    rwa [map_zero, sub_zero] at this
  have hjres0 : R₀.residue ⟨((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')), hjO⟩ ≠ 0 := by rw [hjres]; exact hjbar0
  have hj0 : ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) ≠ 0 := by
    intro h0; apply hjres0
    have : (⟨((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')), hjO⟩ : ↥R₀.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) hj0
  have hlaw := R₀.mapDomain_placeMap ⟨((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')), hjO⟩ hjres0 D hD
  have hC : ∃ P₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'), P₀.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) < 0 ∧ (R₀.placeMap P₀).ord (jGeomGen (ResidueField ↥A) M') < 0 := by
    by_contra hnone
    push_neg at hnone

    have hnonneg : ∀ Q : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M'), 0 ≤ Q.ord (jGeomGen (ResidueField ↥A) M') := by
      intro Q
      by_cases hex : ∃ P, R₀.placeMap P = Q ∧ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ : ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) < 0
      · obtain ⟨P, hPQ, hPneg⟩ := hex
        rw [← hPQ]; exact hnone P hPneg
      · push_neg at hex
        rw [← hjres, ← hlaw Q]
        apply mapDomain_apply_nonneg_of_forall
        intro P hPQ hDP
        rw [hD P] at hDP
        exact absurd (hex P hPQ) (not_le.mpr hDP)
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_forall_ord_nonneg (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') (jGeomGen (ResidueField ↥A) M') hnonneg
    exact jGeomGen_sub_algebraMap_ne_zero (ResidueField ↥A) M' c (by rw [hc, sub_self])
  obtain ⟨P₀, hP₀j, hP₀jbar⟩ := hC

  have hss : (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) ∈ ssPlaces q M' (ResidueField ↥A) := (hW _).mp s.2
  have hss2 : (s' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) ∈ ssPlaces q M' (ResidueField ↥A) := (hW _).mp s'.2
  have hjs : jGeomGen (ResidueField ↥A) M' ∈ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring := hss.2.1.1
  have hjs' : jGeomGen (ResidueField ↥A) M' ∈ (s' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring := hss2.2.1.1
  have hsc : (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) ≠ R₀.placeMap P₀ := by
    intro h
    have h0 := Place.ord_nonneg_of_mem _ hjs
    rw [h] at h0
    omega
  have hs'c : (s' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) ≠ R₀.placeMap P₀ := by
    intro h
    have h0 := Place.ord_nonneg_of_mem _ hjs'
    rw [h] at h0
    omega
  have hss'' : (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) ≠ (s' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) :=
    fun h => hss' (Subtype.ext h)

  obtain ⟨g, hgL, hgs, hgs'⟩ :=
    AlgebraicCurve.exists_mem_riemannRochSpace_smul_single_ord_pos_and_ord_eq_zero (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M')
      (R₀.placeMap P₀) s s' hsc hs'c hss''

  obtain ⟨f, hfO, hfL, hfg⟩ :=
    ModularCurve.FullLevel.exists_mem_integers_riemannRochSpace_residue_eq_of_mem_riemannRochSpace_placeMap
      q M' hqM' A hA R₀ hR₀ P₀ (2 * genusFF (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) M') + 1 + 2 * genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M')) (by omega) g (by
        rw [mem_riemannRochSpace_iff] at hgL ⊢
        intro v
        rcases hgL v with h0 | h
        · exact Or.inl h0
        · right
          refine le_trans ?_ h
          simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
          split_ifs
          · push_cast; omega
          · simp)
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hgs; exact lt_irrefl _ hgs
  refine ⟨f, hfO, ?_, ?_, ?_, ?_⟩
  ·
    intro P hPj
    have hPne : P ≠ P₀ := by intro h; rw [h] at hPj; omega
    rcases (mem_riemannRochSpace_iff.mp hfL) P with h0 | h
    · rw [h0, Place.ord_zero]
    · refine le_trans ?_ h
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, if_neg (Ne.symm hPne)]
      simp
  · rw [hfg]; exact Place.mem_of_ord_nonneg _ hg0 hgs.le
  · rw [hfg]; exact Place.mem_of_ord_nonneg _ hg0 hgs'.ge
  · rw [hfg]
    have hval0 : (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).evalAt g = 0 := by
      have hmem : g ∈ (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).toValuationSubring :=
        Place.mem_of_ord_nonneg _ hg0 hgs.le
      have h := Place.evalAt_congr (s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')) hmem
        ((s : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).algebraMap_mem' 0)
        (Or.inr (by rw [map_zero, sub_zero]; exact hgs))
      rw [h, Place.evalAt_algebraMap]
    have hval1 : (s' : Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) M')).evalAt g ≠ 0 :=
      Place.evalAt_ne_zero _ hss2.1 hg0 hgs'
    rw [hval0]
    exact fun h => hval1 h.symm

end S_ModularCurve_FullLevel_exists_cuspRegular_separating
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_cuspRegular_separating (solution)
