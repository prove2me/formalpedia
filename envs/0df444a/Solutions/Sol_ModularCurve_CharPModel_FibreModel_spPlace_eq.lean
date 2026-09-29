-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spPlace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5bdc1bc8-3f82-5f2a-9219-5f5d118b0292

import Mathlib
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv
import Theorems.Thm_ModularCurve_exists_regularProlongation_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_CharPModel_exists_integral_lift_jChart_and_jInvChart
import Theorems.Thm_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits
import Theorems.Thm_ModularCurve_modularFunctionFieldC_eq_modularFunctionFieldFullC
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_CompEq_finrank_adjoin_jBar_eq_dedekindPsi
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 3200000
set_option Elab.async false

p2m_open "AlgebraicCurve~genus ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq.ModularCurve.CharPModel IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem qExpand jq dedekindPsi ModularPolynomialData jq_mem modularFunctionField_le_full coeffMap coeffEmb coeffEmb_mem_laurentBaseChange CharPModel.jBar CharPModel.FibreModel modularFunctionFieldBar CharPReduction.mem_integralCoeffs CharPReduction.coeffRed CharPReduction.redRes CharPReduction.redKer CharPReduction.redLoc CharPReduction.redRes_ne_zero_of_notMem CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom exists_regularProlongation_modularFunctionFieldBar coeffMap_jqModC coeffMap_jqNModC jqModC_mem_full CharPModel.exists_integral_lift_jChart_and_jInvChart modularFunctionFieldC_eq_modularFunctionFieldFullC transcendental_jqModC CompEq.finrank_adjoin_jBar_eq_dedekindPsi jBar finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi isCurveOver_modularFunctionFieldC_of_perfectField isCurveOver_modularFunctionFieldBar"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar jNBar FibreModel FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv exists_integral_lift_jChart_and_jInvChart"
namespace SolINV
p2m_open "ModularCurve.CharPModel ModularCurve"

noncomputable section

private def jBarE (N : ℕ) [NeZero N] : modularFunctionFieldBar N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq,
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularFunctionField_le_full N (jq_mem N))⟩

private def jCE (k : Type*) [Field k] (N : ℕ) [NeZero N] : modularFunctionFieldC k N :=
  ⟨jqModC k, jqModC_mem k N⟩

private theorem jBarE_eq (N : ℕ) [NeZero N] : jBarE N = jBar N :=
  Subtype.ext rfl

private def mapResidueRP {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Field Fbar'] [Algebra (ResidueField A) Fbar]
    [Algebra (ResidueField A) Fbar'] (R : RegularProlongation A F Fbar)
    (e : Fbar ≃ₐ[ResidueField A] Fbar') : RegularProlongation A F Fbar' where
  integers := R.integers
  residue := (e : Fbar →+* Fbar').comp R.residue
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := e.surjective.comp R.residue_surjective
  ker_residue := by
    rw [RingHom.ker_comp_of_injective _ (by exact e.injective)]
    exact R.ker_residue
  residue_algebraMap a := by
    rw [RingHom.comp_apply, R.residue_algebraMap]
    exact e.commutes _
  exists_smul_mem f hf := by
    obtain ⟨c, h, hne⟩ := R.exists_smul_mem f hf
    exact ⟨c, h, by rwa [RingHom.comp_apply, RingHom.coe_coe, map_ne_zero_iff _ e.injective]⟩

private theorem liesOverPrime_of_charP' {L : Type*} [Field L] (A : ValuationSubring L) (ℓ : ℕ)
    [CharP (ResidueField A) ℓ] : A.LiesOverPrime ℓ := by
  show ((ℓ : A) : L) ∈ A.nonunits
  rw [ValuationSubring.coe_mem_nonunits_iff, ← Ideal.Quotient.eq_zero_iff_mem]
  show IsLocalRing.residue A (ℓ : A) = 0
  rw [map_natCast]
  exact CharP.cast_eq_zero _ ℓ

private theorem one_le_dedekindPsi' (N : ℕ) [NeZero N] : 1 ≤ dedekindPsi N := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  refine hN.trans ?_
  unfold dedekindPsi
  have hmem : 1 ∈ N.divisors.filter Squarefree :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr (NeZero.ne N), squarefree_one⟩
  have := Finset.single_le_sum (f := fun d => N / d) (fun _ _ => Nat.zero_le _) hmem
  simpa using this

private theorem finrank_adjoin_singleton_congr' {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h : S = T) (z : E) (hS : z ∈ S) (hT : z ∈ T) :
    Module.finrank (IntermediateField.adjoin K ({(⟨z, hS⟩ : S)} : Set S)) S =
      Module.finrank (IntermediateField.adjoin K ({(⟨z, hT⟩ : T)} : Set T)) T := by
  subst h; rfl

private theorem finrank_adjoin_elem_congr' {K E : Type*} [Field K] [Field E] [Algebra K E]
    {a b : E} (h : a = b) :
    Module.finrank (IntermediateField.adjoin K ({a} : Set E)) E =
      Module.finrank (IntermediateField.adjoin K ({b} : Set E)) E := by
  subst h; rfl

private theorem finrank_congr_of_eq' {K E : Type*} [Field K] [Field E] [Algebra K E]
    {S T : IntermediateField K E} (h : S = T) : Module.finrank S E = Module.finrank T E := by
  subst h; rfl

private theorem isIntegral_adjoin_singleton_congr' {K E : Type*} [Field K] [Field E] [Algebra K E]
    {a b : E} (h : a = b) (x : E) :
    IsIntegral (Algebra.adjoin K ({a} : Set E)) x ↔ IsIntegral (Algebra.adjoin K ({b} : Set E)) x := by
  subst h; rfl

private theorem adjoin_simple_inv' {K E : Type*} [Field K] [Field E] [Algebra K E] (z : E) :
    IntermediateField.adjoin K ({z⁻¹} : Set E) = IntermediateField.adjoin K ({z} : Set E) := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr (inv_mem (IntermediateField.mem_adjoin_simple_self K z))
  · refine IntermediateField.adjoin_simple_le_iff.mpr ?_
    simpa only [inv_inv] using inv_mem (IntermediateField.mem_adjoin_simple_self K z⁻¹)

private theorem inv_mem_integers_of_residue_ne_zero' {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (x : R.integers) (hx : R.residue x ≠ 0) :
    ∃ hinv : (x : F)⁻¹ ∈ R.integers, R.residue ⟨(x : F)⁻¹, hinv⟩ = (R.residue x)⁻¹ := by
  have hunit : IsUnit x := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← R.ker_residue, RingHom.mem_ker]
    exact hx
  obtain ⟨u, hu⟩ := hunit
  have hx0 : (x : F) ≠ 0 := by
    intro h0
    apply hx
    rw [show x = 0 from Subtype.ext h0, map_zero]
  have hinv : (x : F)⁻¹ = ((u⁻¹ : R.integersˣ) : R.integers) := by
    rw [inv_eq_iff_eq_inv, ← hu]
    symm
    apply inv_eq_of_mul_eq_one_right
    rw [← Subring.coe_mul, show ((u⁻¹ : R.integersˣ) : R.integers) * (u : R.integers) = 1 from Units.inv_mul u,
      OneMemClass.coe_one]
  refine ⟨hinv ▸ ((u⁻¹ : R.integersˣ) : R.integers).2, ?_⟩
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul]
  have : x * ⟨(x : F)⁻¹, hinv ▸ ((u⁻¹ : R.integersˣ) : R.integers).2⟩ = 1 :=
    Subtype.ext (by rw [Subring.coe_mul, OneMemClass.coe_one]; exact mul_inv_cancel₀ hx0)
  rw [this, map_one]

section Bridge

variable (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))

private def packA' (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    LaurentSeries A where
  coeff n := ⟨x.coeff n, hx n⟩
  isPWO_support' := x.isPWO_support.mono (fun _ hn h => hn (Subtype.ext h))

private theorem coeffMap_subtype_packA' (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : ∀ n : ℤ, x.coeff n ∈ A) : coeffMap A.subtype (packA' A x hx) = x := by
  ext n; rfl

private theorem coeffMap_residue_packA' (x : LaurentSeries (AlgebraicClosure ℚ))
    (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    coeffMap (IsLocalRing.residue A) (packA' A x hx)
      = CharPReduction.coeffRed A.toSubring (IsLocalRing.residue A) ⟨x, hx⟩ := by
  ext n; rfl

private theorem modularRing_le_bar' :
    CharPReduction.modularRing N A.toSubring ≤ (modularFunctionFieldBar N).toSubring := by
  rw [CharPReduction.modularRing, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | rfl | rfl)
  · exact (modularFunctionFieldBar N).algebraMap_mem (a : AlgebraicClosure ℚ)
  · have e : jqModC (AlgebraicClosure ℚ)
        = ((jBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
      show _ = coeffEmb (AlgebraicClosure ℚ) jq
      rw [← jqModC_rat]
      exact (coeffMap_jqModC _).symm
    rw [e]
    exact (jBar N).2
  · have e : jqNModC (AlgebraicClosure ℚ) N
        = ((jNBar N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
      show _ = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq)
      rw [show qExpand ℚ N jq = jqNModC ℚ N from rfl]
      exact (coeffMap_jqNModC _ N).symm
    rw [e]
    exact (jNBar N).2

private theorem integers_of_modularRing'
    (R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) N)
            : LaurentSeries (ResidueField A))
          = coeffMap (IsLocalRing.residue A) y)
    (r : CharPReduction.modularRing N A.toSubring) :
    ∃ hr : (⟨(r : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A r.2⟩ :
        modularFunctionFieldBar N) ∈ R.integers,
      ((R.residue ⟨_, hr⟩ : modularFunctionFieldC (ResidueField A) N)
          : LaurentSeries (ResidueField A))
        = CharPReduction.redRes A.toSubring (IsLocalRing.residue A)
            (CharPReduction.modularRing N A.toSubring)
            (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) r := by
  have hrI : ∀ n : ℤ, (r : LaurentSeries (AlgebraicClosure ℚ)).coeff n ∈ A :=
    (CharPReduction.mem_integralCoeffs _).mp
      (CharPReduction.modularRing_le_integralCoeffs N A.toSubring r.2)
  have hyr : coeffMap A.subtype (packA' A r hrI) = r := coeffMap_subtype_packA' A r hrI
  have hyrB : coeffMap A.subtype (packA' A r hrI) ∈ modularFunctionFieldBar N := by
    rw [hyr]; exact modularRing_le_bar' N A r.2
  obtain ⟨hint, hres⟩ := hspec _ hyrB
  have e : (⟨coeffMap A.subtype (packA' A r hrI), hyrB⟩ : modularFunctionFieldBar N)
      = ⟨(r : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A r.2⟩ :=
    Subtype.ext hyr
  have hr : (⟨(r : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A r.2⟩ :
      modularFunctionFieldBar N) ∈ R.integers := by
    rw [← e]; exact hint
  refine ⟨hr, ?_⟩
  have e2 : (⟨⟨(r : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A r.2⟩, hr⟩ :
      R.integers) = ⟨_, hint⟩ := Subtype.ext e.symm
  rw [e2, hres, coeffMap_residue_packA']
  rfl

private theorem bridge_core'
    (R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) N)
            : LaurentSeries (ResidueField A))
          = coeffMap (IsLocalRing.residue A) y)
    (u : R.integers) (T : LaurentSeries (AlgebraicClosure ℚ))
    (hT : ((u : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) = T)
    (e : modularFunctionFieldC (ResidueField A) N) (he : R.residue u = e)
    (Tk : LaurentSeries (ResidueField A))
    (hTk : (e : LaurentSeries (ResidueField A)) = Tk)
    (H : ∀ y : LaurentSeries (ResidueField A), y ∈ modularFunctionFieldC (ResidueField A) N →
      (∃ P : Polynomial (Polynomial (ResidueField A)), P.Monic ∧
        Polynomial.eval₂ (Polynomial.eval₂RingHom
          (algebraMap (ResidueField A) (LaurentSeries (ResidueField A))) Tk) y P = 0) →
      ∃ f : CharPReduction.modularLocalized N A.toSubring (IsLocalRing.residue A),
        (∃ P : Polynomial (Polynomial A), P.Monic ∧
          Polynomial.eval₂ (Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
              A.subtype) T) (f : LaurentSeries (AlgebraicClosure ℚ)) P = 0) ∧
        CharPReduction.modularRedLocHom N A.toSubring (IsLocalRing.residue A) f = y)
    (h : modularFunctionFieldC (ResidueField A) N)
    (hh : IsIntegral (Algebra.adjoin (ResidueField A) {e}) h) :
    ∃ f : R.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {(u : modularFunctionFieldBar N)})
        (f : modularFunctionFieldBar N) ∧ R.residue f = h := by
  subst he hTk hT
  classical

  obtain ⟨Q, hQm, hQ⟩ := hh
  have hS : ∀ p : Polynomial (ResidueField A), Polynomial.aeval (R.residue u) p ∈
      Algebra.adjoin (ResidueField A) {R.residue u} := fun p => by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact (Polynomial.aeval _).mem_range_self p
  let ψ : Polynomial (ResidueField A) →ₐ[ResidueField A]
      Algebra.adjoin (ResidueField A) {R.residue u} :=
    (Polynomial.aeval (R.residue u)).codRestrict _ hS
  have hψ : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨p, hp⟩ := (AlgHom.mem_range _).mp hc
    exact ⟨p, Subtype.ext hp⟩
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective ψ.toRingHom hψ Q)) hQm
  rw [← hPmap, Polynomial.eval₂_map] at hQ
  have hcomp : (algebraMap (Algebra.adjoin (ResidueField A) {R.residue u})
      (modularFunctionFieldC (ResidueField A) N)).comp ψ.toRingHom
      = Polynomial.eval₂RingHom (algebraMap (ResidueField A)
          (modularFunctionFieldC (ResidueField A) N)) (R.residue u) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      show ((Polynomial.aeval (R.residue u) (Polynomial.C a) :
        modularFunctionFieldC (ResidueField A) N)) = _
      rw [Polynomial.aeval_C]
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      show ((Polynomial.aeval (R.residue u) Polynomial.X :
        modularFunctionFieldC (ResidueField A) N)) = _
      rw [Polynomial.aeval_X]
  rw [hcomp] at hQ
  have hQ' := congrArg (algebraMap (modularFunctionFieldC (ResidueField A) N)
    (LaurentSeries (ResidueField A))) hQ
  rw [map_zero, Polynomial.hom_eval₂] at hQ'
  have hcomp2 : (algebraMap (modularFunctionFieldC (ResidueField A) N)
      (LaurentSeries (ResidueField A))).comp (Polynomial.eval₂RingHom
        (algebraMap (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) (R.residue u))
      = Polynomial.eval₂RingHom (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)))
          ((R.residue u : modularFunctionFieldC (ResidueField A) N) :
            LaurentSeries (ResidueField A)) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C, Polynomial.eval₂_C]
      rfl
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X, Polynomial.eval₂_X]
      rfl
  rw [hcomp2] at hQ'

  obtain ⟨f, ⟨P', hP'm, hP'⟩, hredf⟩ := H (h : LaurentSeries (ResidueField A)) h.2 ⟨P, hPm, hQ'⟩

  obtain ⟨r, s, hs, hfs⟩ : ∃ r s : CharPReduction.modularRing N A.toSubring,
      s ∉ CharPReduction.redKer A.toSubring (IsLocalRing.residue A)
        (CharPReduction.modularRing N A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs N A.toSubring) ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * s = r := f.2
  have hsne := CharPReduction.redRes_ne_zero_of_notMem hs
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    intro h0
    apply hsne
    rw [show s = 0 from Subtype.ext h0, map_zero]
  obtain ⟨hr, hres_r⟩ := integers_of_modularRing' N A R hspec r
  obtain ⟨hsI, hres_s⟩ := integers_of_modularRing' N A R hspec s
  have hres_s0 : R.residue ⟨_, hsI⟩ ≠ 0 := by
    intro h0
    apply hsne
    rw [← hres_s, h0]
    rfl
  obtain ⟨hinv, hinvres⟩ := inv_mem_integers_of_residue_ne_zero' R ⟨_, hsI⟩ hres_s0
  have hinv' : ((⟨(s : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A s.2⟩ :
      modularFunctionFieldBar N))⁻¹ ∈ R.integers := hinv
  have hinvres' : R.residue ⟨((⟨(s : LaurentSeries (AlgebraicClosure ℚ)),
      modularRing_le_bar' N A s.2⟩ : modularFunctionFieldBar N))⁻¹, hinv'⟩
        = (R.residue ⟨_, hsI⟩)⁻¹ := hinvres

  have hfB : algebraMap (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))
      ((⟨(r : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A r.2⟩ :
          modularFunctionFieldBar N) *
        ((⟨(s : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A s.2⟩ :
          modularFunctionFieldBar N))⁻¹)
      = (f : LaurentSeries (AlgebraicClosure ℚ)) := by
    show (((⟨(r : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A r.2⟩ :
          modularFunctionFieldBar N) *
        ((⟨(s : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A s.2⟩ :
          modularFunctionFieldBar N))⁻¹ : modularFunctionFieldBar N) :
            LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [IntermediateField.coe_mul, IntermediateField.coe_inv]
    exact ((eq_mul_inv_iff_mul_eq₀ hs0).mpr hfs).symm
  refine ⟨⟨_, mul_mem hr hinv'⟩, ?_, ?_⟩
  ·
    have hS' : ∀ p : Polynomial (AlgebraicClosure ℚ),
        Polynomial.aeval (u : modularFunctionFieldBar N) p ∈
          Algebra.adjoin (AlgebraicClosure ℚ) {(u : modularFunctionFieldBar N)} := fun p => by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact (Polynomial.aeval _).mem_range_self p
    let θ : Polynomial A →+*
        Algebra.adjoin (AlgebraicClosure ℚ) {(u : modularFunctionFieldBar N)} :=
      ((Polynomial.aeval (u : modularFunctionFieldBar N)).codRestrict _ hS').toRingHom.comp
        (Polynomial.mapRingHom A.subtype)
    refine ⟨P'.map θ, hP'm.map θ, ?_⟩
    rw [Polynomial.eval₂_map]
    apply (algebraMap (modularFunctionFieldBar N) (LaurentSeries (AlgebraicClosure ℚ))).injective
    rw [map_zero, Polynomial.hom_eval₂]
    have hcomp3 : (algebraMap (modularFunctionFieldBar N)
        (LaurentSeries (AlgebraicClosure ℚ))).comp ((algebraMap
          (Algebra.adjoin (AlgebraicClosure ℚ) {(u : modularFunctionFieldBar N)})
          (modularFunctionFieldBar N)).comp θ)
        = Polynomial.eval₂RingHom
            ((algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).comp
              A.subtype)
            ((u : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) := by
      apply Polynomial.ringHom_ext
      · intro a
        rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
          RingHom.comp_apply]
        show (((Polynomial.aeval (u : modularFunctionFieldBar N))
          (Polynomial.mapRingHom A.subtype (Polynomial.C a)) : modularFunctionFieldBar N) :
            LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.aeval_C]
        rfl
      · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.comp_apply,
          RingHom.comp_apply]
        show (((Polynomial.aeval (u : modularFunctionFieldBar N))
          (Polynomial.mapRingHom A.subtype Polynomial.X) : modularFunctionFieldBar N) :
            LaurentSeries (AlgebraicClosure ℚ)) = _
        rw [Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.aeval_X]
    rw [hcomp3]
    show Polynomial.eval₂ _ (algebraMap (modularFunctionFieldBar N)
      (LaurentSeries (AlgebraicClosure ℚ)) ((⟨(r : LaurentSeries (AlgebraicClosure ℚ)),
          modularRing_le_bar' N A r.2⟩ : modularFunctionFieldBar N) *
        ((⟨(s : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A s.2⟩ :
          modularFunctionFieldBar N))⁻¹)) P' = 0
    rw [hfB]
    exact hP'
  ·
    apply (algebraMap (modularFunctionFieldC (ResidueField A) N)
      (LaurentSeries (ResidueField A))).injective
    have e1 : (⟨_, mul_mem hr hinv'⟩ : R.integers)
        = ⟨_, hr⟩ * ⟨((⟨(s : LaurentSeries (AlgebraicClosure ℚ)), modularRing_le_bar' N A s.2⟩ :
            modularFunctionFieldBar N))⁻¹, hinv'⟩ := rfl
    rw [e1, map_mul, hinvres', map_mul, map_inv₀,
      show algebraMap _ (LaurentSeries (ResidueField A)) (R.residue ⟨_, hr⟩) = _ from hres_r,
      show algebraMap _ (LaurentSeries (ResidueField A)) (R.residue ⟨_, hsI⟩) = _ from hres_s]
    show _ = (h : LaurentSeries (ResidueField A))
    rw [← hredf]
    show _ = CharPReduction.redLoc f
    symm
    exact (eq_mul_inv_iff_mul_eq₀ hsne).mpr (CharPReduction.redLoc_spec f hfs)

private theorem legFIN' (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField A) ℓ] (hℓN : ¬ ℓ ∣ N)
    (R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) N)
            : LaurentSeries (ResidueField A))
          = coeffMap (IsLocalRing.residue A) y)
    (xj : R.integers) (hxj : (xj : modularFunctionFieldBar N) = jBarE N)
    (hxjres : R.residue xj = jCE (ResidueField A) N) :
    ∀ h : modularFunctionFieldC (ResidueField A) N,
      IsIntegral (Algebra.adjoin (ResidueField A) {R.residue xj}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          {(xj : modularFunctionFieldBar N)}) (f : modularFunctionFieldBar N) ∧
          R.residue f = h := by
  intro h hh
  have hcoe : ((xj : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := by
    rw [hxj]
    show coeffEmb (AlgebraicClosure ℚ) jq = _
    rw [← jqModC_rat]
    exact coeffMap_jqModC _
  have hTk : ((R.residue xj : modularFunctionFieldC (ResidueField A) N) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
    rw [hxjres]; rfl
  exact bridge_core' N A R hspec xj _ hcoe (R.residue xj) rfl _ hTk
    (exists_integral_lift_jChart_and_jInvChart N A ℓ hℓN (ResidueField A)
      (IsLocalRing.residue A) IsLocalRing.residue_surjective).1 h hh

private theorem legINF' (ℓ : ℕ) [Fact ℓ.Prime] [CharP (ResidueField A) ℓ] (hℓN : ¬ ℓ ∣ N)
    (R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField A) N))
    (hspec : ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
      ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
        ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) N)
            : LaurentSeries (ResidueField A))
          = coeffMap (IsLocalRing.residue A) y)
    (xj : R.integers) (hxj : (xj : modularFunctionFieldBar N) = jBarE N)
    (hxjres : R.residue xj = jCE (ResidueField A) N) :
    ∀ h : modularFunctionFieldC (ResidueField A) N,
      IsIntegral (Algebra.adjoin (ResidueField A) {(R.residue xj)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          {((xj : modularFunctionFieldBar N))⁻¹}) (f : modularFunctionFieldBar N) ∧
          R.residue f = h := by
  intro h hh
  have hcoe : ((xj : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := by
    rw [hxj]
    show coeffEmb (AlgebraicClosure ℚ) jq = _
    rw [← jqModC_rat]
    exact coeffMap_jqModC _
  have hTk : ((R.residue xj : modularFunctionFieldC (ResidueField A) N) :
      LaurentSeries (ResidueField A)) = jqModC (ResidueField A) := by
    rw [hxjres]; rfl
  have hxj0 : R.residue xj ≠ 0 := by
    rw [hxjres]
    intro h0
    apply transcendental_jqModC (ResidueField A)
    rw [show jqModC (ResidueField A) = 0 from congrArg Subtype.val h0]
    exact isAlgebraic_zero
  obtain ⟨hinv, hinvres⟩ := inv_mem_integers_of_residue_ne_zero' R xj hxj0
  have hT : (((⟨((xj : modularFunctionFieldBar N))⁻¹, hinv⟩ : R.integers) :
      modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
        = (jqModC (AlgebraicClosure ℚ))⁻¹ := by
    show ((((xj : modularFunctionFieldBar N))⁻¹ : modularFunctionFieldBar N) :
      LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [IntermediateField.coe_inv, hcoe]
  have hTk' : (((R.residue xj)⁻¹ : modularFunctionFieldC (ResidueField A) N) :
      LaurentSeries (ResidueField A)) = (jqModC (ResidueField A))⁻¹ := by
    rw [IntermediateField.coe_inv, hTk]
  exact bridge_core' N A R hspec ⟨_, hinv⟩ _ hT _ hinvres _ hTk'
    (exists_integral_lift_jChart_and_jInvChart N A ℓ hℓN (ResidueField A)
      (IsLocalRing.residue A) IsLocalRing.residue_surjective).2 h hh

end Bridge

section RC
variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
  (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField A) ℓ]

private theorem exists_RC_full' (hℓN : ¬ ℓ ∣ N) :
    ∃ R : RegularProlongation A (modularFunctionFieldBar N)
        (modularFunctionFieldC (ResidueField A) N),
      (∀ (y : LaurentSeries A)
          (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) N)
              : LaurentSeries (ResidueField A))
            = coeffMap (IsLocalRing.residue A) y) ∧
      (∃ xj : R.integers, (xj : modularFunctionFieldBar N) = jBarE N ∧
        R.residue xj = jCE (ResidueField A) N ∧
        Transcendental (ResidueField A) (R.residue xj) ∧
        0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
          ({R.residue xj} : Set (modularFunctionFieldC (ResidueField A) N)))
          (modularFunctionFieldC (ResidueField A) N) ∧
        Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({(xj : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
            (modularFunctionFieldBar N) =
          Module.finrank (IntermediateField.adjoin (ResidueField A)
            ({R.residue xj} : Set (modularFunctionFieldC (ResidueField A) N)))
            (modularFunctionFieldC (ResidueField A) N) ∧
        (∀ h : modularFunctionFieldC (ResidueField A) N,
          IsIntegral (Algebra.adjoin (ResidueField A) {R.residue xj}) h →
            ∃ f : R.integers,
              IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
                {(xj : modularFunctionFieldBar N)}) (f : modularFunctionFieldBar N) ∧
              R.residue f = h)) ∧
      (∃ xinf : R.integers, (xinf : modularFunctionFieldBar N) = (jBarE N)⁻¹ ∧
        R.residue xinf = (jCE (ResidueField A) N)⁻¹ ∧
        Transcendental (ResidueField A) (R.residue xinf) ∧
        0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
          ({R.residue xinf} : Set (modularFunctionFieldC (ResidueField A) N)))
          (modularFunctionFieldC (ResidueField A) N) ∧
        Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
            ({(xinf : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)))
            (modularFunctionFieldBar N) =
          Module.finrank (IntermediateField.adjoin (ResidueField A)
            ({R.residue xinf} : Set (modularFunctionFieldC (ResidueField A) N)))
            (modularFunctionFieldC (ResidueField A) N) ∧
        (∀ h : modularFunctionFieldC (ResidueField A) N,
          IsIntegral (Algebra.adjoin (ResidueField A) {R.residue xinf}) h →
            ∃ f : R.integers,
              IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
                {(xinf : modularFunctionFieldBar N)}) (f : modularFunctionFieldBar N) ∧
              R.residue f = h)) := by
  have hCF := modularFunctionFieldC_eq_modularFunctionFieldFullC (ResidueField A) ℓ N hℓN
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  have hNk : (N : ResidueField A) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff (ResidueField A) ℓ N).mp h)
  obtain ⟨R, hspec⟩ : ∃ R : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField A) N),
      ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar N),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : modularFunctionFieldBar N) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : modularFunctionFieldC (ResidueField A) N) : LaurentSeries (ResidueField A))
            = coeffMap (IsLocalRing.residue A) y := by
    obtain ⟨R₀, hR₀⟩ := exists_regularProlongation_modularFunctionFieldBar N hℓN A (liesOverPrime_of_charP' A ℓ)
    refine ⟨mapResidueRP R₀ (IntermediateField.equivOfEq hCF.symm), fun y hy => ?_⟩
    obtain ⟨hint, h⟩ := hR₀ y hy
    exact ⟨hint, h⟩
  have hcoe : ((jBarE N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ)) =
      jqModC (AlgebraicClosure ℚ) := by
    show coeffEmb (AlgebraicClosure ℚ) jq = _
    rw [← jqModC_rat]; exact coeffMap_jqModC _
  have hyA : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar N := by
    rw [coeffMap_jqModC, ← hcoe]; exact (jBarE N).2
  have hel : (⟨coeffMap A.subtype (jqModC A), hyA⟩ : modularFunctionFieldBar N) = jBarE N := by
    apply Subtype.ext
    show coeffMap A.subtype (jqModC A) = ((jBarE N : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
    rw [hcoe, coeffMap_jqModC]
  obtain ⟨hint, hres⟩ := hspec (jqModC A) hyA
  have hj : (jBarE N : modularFunctionFieldBar N) ∈ R.integers := by rw [← hel]; exact hint
  let xj : R.integers := ⟨jBarE N, hj⟩
  have hxjres : R.residue xj = jCE (ResidueField A) N := by
    have e1 : xj = ⟨_, hint⟩ := Subtype.ext hel.symm
    rw [e1]
    apply Subtype.ext
    rw [hres, coeffMap_jqModC]
    rfl
  have hxjt : Transcendental (ResidueField A) (R.residue xj) := by
    rw [hxjres]
    intro halg
    exact transcendental_jqModC (ResidueField A) (halg.algebraMap (A := LaurentSeries (ResidueField A)))
  have hfinC : Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({R.residue xj} : Set (modularFunctionFieldC (ResidueField A) N))) (modularFunctionFieldC (ResidueField A) N)
      = dedekindPsi N := by
    refine (finrank_adjoin_elem_congr' hxjres).trans ?_
    refine (finrank_adjoin_singleton_congr' hCF (jqModC (ResidueField A)) (jqModC_mem (ResidueField A) N)
      (jqModC_mem_full (ResidueField A) N)).trans ?_
    exact finrank_adjoin_jqModC_modularFunctionFieldFullC_eq_dedekindPsi (ResidueField A) N hNk
  have hfinBar : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(xj : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = dedekindPsi N := by
    refine (finrank_adjoin_elem_congr' (show (xj : modularFunctionFieldBar N) = ModularCurve.jBar N from
      Subtype.ext rfl)).trans ?_
    exact CompEq.finrank_adjoin_jBar_eq_dedekindPsi N
  have hfin : 0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({R.residue xj} : Set (modularFunctionFieldC (ResidueField A) N))) (modularFunctionFieldC (ResidueField A) N) :=
    hfinC ▸ one_le_dedekindPsi' N
  have hdeg : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
      ({(xj : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))) (modularFunctionFieldBar N)
      = Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({R.residue xj} : Set (modularFunctionFieldC (ResidueField A) N))) (modularFunctionFieldC (ResidueField A) N) :=
    hfinBar.trans hfinC.symm

  have hFIN : ∀ h : modularFunctionFieldC (ResidueField A) N,
      IsIntegral (Algebra.adjoin (ResidueField A) {R.residue xj}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          {(xj : modularFunctionFieldBar N)}) (f : modularFunctionFieldBar N) ∧
          R.residue f = h :=
    legFIN' N A ℓ hℓN R hspec xj rfl hxjres
  have hINF : ∀ h : modularFunctionFieldC (ResidueField A) N,
      IsIntegral (Algebra.adjoin (ResidueField A) {(R.residue xj)⁻¹}) h →
        ∃ f : R.integers, IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          {((xj : modularFunctionFieldBar N))⁻¹}) (f : modularFunctionFieldBar N) ∧
          R.residue f = h :=
    legINF' N A ℓ hℓN R hspec xj rfl hxjres
  have hxj0 : R.residue xj ≠ 0 := fun h0 => hxjt (h0 ▸ isAlgebraic_zero)
  obtain ⟨hinvmem, hinvres⟩ := inv_mem_integers_of_residue_ne_zero' R xj hxj0
  let xinf : R.integers := ⟨(xj : modularFunctionFieldBar N)⁻¹, hinvmem⟩
  have hxinfres : R.residue xinf = (R.residue xj)⁻¹ := hinvres
  have hxinft : Transcendental (ResidueField A) (R.residue xinf) := by
    rw [hxinfres]
    exact fun halg => hxjt (IsAlgebraic.inv_iff.mp halg)
  have hadjk : IntermediateField.adjoin (ResidueField A) ({R.residue xinf} : Set (modularFunctionFieldC (ResidueField A) N))
      = IntermediateField.adjoin (ResidueField A) ({R.residue xj} : Set (modularFunctionFieldC (ResidueField A) N)) := by
    rw [hxinfres]; exact adjoin_simple_inv' _
  have hadjL : IntermediateField.adjoin (AlgebraicClosure ℚ) ({(xinf : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N))
      = IntermediateField.adjoin (AlgebraicClosure ℚ) ({(xj : modularFunctionFieldBar N)} : Set (modularFunctionFieldBar N)) :=
    adjoin_simple_inv' _
  refine ⟨R, hspec, ⟨xj, rfl, hxjres, hxjt, hfin, hdeg, hFIN⟩, ⟨xinf, rfl, ?_, hxinft, ?_, ?_, ?_⟩⟩
  · rw [hxinfres, hxjres]
  · exact (finrank_congr_of_eq' hadjk).symm ▸ hfin
  · exact (finrank_congr_of_eq' hadjL).trans (hdeg.trans (finrank_congr_of_eq' hadjk).symm)
  · intro h hh
    rw [isIntegral_adjoin_singleton_congr' hxinfres] at hh
    exact hINF h hh

end RC

section Dich
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

private theorem algebraMap_mem'' (a : K) : algebraMap K F a ∈ w.toValuationSubring :=
  w.algebraMap_mem' a

private theorem algebraMap_mem_nonunits_iff'' (a : K) :
    algebraMap K F a ∈ w.toValuationSubring.nonunits ↔ a = 0 := by
  constructor
  · intro h
    rcases (ValuationSubring.mem_nonunits_iff_or _).mp h with h0 | hinv
    · exact (map_eq_zero _).mp h0
    · exact absurd (by simpa using algebraMap_mem'' w a⁻¹) hinv
  · rintro rfl
    simp [ZeroMemClass.zero_mem]

private theorem mul_mem_nonunits'' {x y : F} (hx : x ∈ w.toValuationSubring.nonunits)
    (hy : y ∈ w.toValuationSubring) : x * y ∈ w.toValuationSubring.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hx ⊢
  rw [← ValuationSubring.valuation_le_one_iff] at hy
  calc w.toValuationSubring.valuation (x * y)
      = w.toValuationSubring.valuation x * w.toValuationSubring.valuation y := map_mul _ _ _
    _ ≤ w.toValuationSubring.valuation x * 1 := by gcongr
    _ = w.toValuationSubring.valuation x := mul_one _
    _ < 1 := hx

private theorem mem_of_ord_pos' {f : F} (h : 0 < w.ord f) : f ∈ w.toValuationSubring := by
  have hf : f ≠ 0 := by rintro rfl; simp at h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf hπ
  rw [hu, show w.ord f = (((w.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h.le).symm,
    zpow_natCast]
  exact mul_mem (u : w.toValuationSubring).2 (pow_mem (π : w.toValuationSubring).2 _)

private theorem mem_nonunits_iff_ord_pos' {f : F} (hf : f ≠ 0) :
    f ∈ w.toValuationSubring.nonunits ↔ 0 < w.ord f := by
  constructor
  · intro h
    have hmem : f ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
    have h' : ((⟨f, hmem⟩ : w.toValuationSubring) : F) ∈ w.toValuationSubring.nonunits := h
    rw [ValuationSubring.coe_mem_nonunits_iff] at h'
    exact (w.mem_maximalIdeal_iff_ord_pos hf hmem).mp h'
  · intro h
    have hmem : f ∈ w.toValuationSubring := mem_of_ord_pos' w h
    have h' := (w.mem_maximalIdeal_iff_ord_pos hf hmem).mpr h
    rw [← ValuationSubring.coe_mem_nonunits_iff] at h'
    exact h'

private def HasValueAt' (f : F) (a : K) : Prop :=
  f - algebraMap K F a ∈ w.toValuationSubring.nonunits

private theorem hasValueAt_algebraMap' (a : K) : HasValueAt' w (algebraMap K F a) a := by
  simp [HasValueAt', ZeroMemClass.zero_mem]

private theorem hasValueAt_zero_iff' (f : F) :
    HasValueAt' w f 0 ↔ f ∈ w.toValuationSubring.nonunits := by
  simp [HasValueAt']

private theorem mem_of_hasValueAt' {f : F} {a : K} (h : HasValueAt' w f a) :
    f ∈ w.toValuationSubring := by
  have h1 : f - algebraMap K F a ∈ w.toValuationSubring := w.toValuationSubring.nonunits_subset h
  simpa using add_mem h1 (algebraMap_mem'' w a)

variable {w} in
private theorem HasValueAt'.unique' {f : F} {a b : K} (ha : HasValueAt' w f a)
    (hb : HasValueAt' w f b) : a = b := by
  have h : algebraMap K F (a - b) ∈ w.toValuationSubring.nonunits := by
    have := sub_mem hb ha
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact sub_eq_zero.mp ((algebraMap_mem_nonunits_iff'' w _).mp h)

variable {w} in
private theorem HasValueAt'.inv' {f : F} {a : K} (hf : HasValueAt' w f a) (ha : a ≠ 0) :
    HasValueAt' w f⁻¹ a⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have : HasValueAt' w (0 : F) 0 := by simpa using hasValueAt_algebraMap' w 0
    exact ha (hf.unique' this)
  have hfu : f ∉ w.toValuationSubring.nonunits := fun hfn =>
    ha (hf.unique' ((hasValueAt_zero_iff' w f).mpr hfn))
  have hfinv : f⁻¹ ∈ w.toValuationSubring := by
    by_contra hne
    exact hfu ((ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hne)))
  have hprod : (f - algebraMap K F a) * (f⁻¹ * algebraMap K F a⁻¹)
      ∈ w.toValuationSubring.nonunits :=
    mul_mem_nonunits'' w hf (mul_mem hfinv (algebraMap_mem'' w _))
  have := neg_mem hprod
  change f⁻¹ - algebraMap K F a⁻¹ ∈ w.toValuationSubring.nonunits
  convert this using 1
  have haF : algebraMap K F a ≠ 0 := by simpa using ha
  rw [map_inv₀]
  field_simp
  ring

private theorem hasValueAt_iff_residue' {f : F} (hf : f ∈ w.toValuationSubring) (a : K) :
    HasValueAt' w f a ↔
      residue w.toValuationSubring ⟨f, hf⟩ = algebraMap K w.ResidueField a := by
  have e : algebraMap K w.ResidueField a =
      residue w.toValuationSubring (algebraMap K w.toValuationSubring a) := rfl
  rw [e, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

private theorem exists_hasValueAt' (hw : Function.Surjective (algebraMap K w.ResidueField))
    {f : F} (hf : f ∈ w.toValuationSubring) : ∃ a : K, HasValueAt' w f a := by
  obtain ⟨a, ha⟩ := hw (residue w.toValuationSubring ⟨f, hf⟩)
  exact ⟨a, (hasValueAt_iff_residue' w hf a).mpr ha.symm⟩

private theorem surjective_residueField_of_deg_eq_one' [IsAlgClosed K] (h : w.deg = 1) :
    Function.Surjective (algebraMap K w.ResidueField) :=
  haveI : Module.Finite K w.ResidueField := Module.finite_of_finrank_eq_succ (n := 0) h
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K w.ResidueField
  (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

end Dich

section DichApp
variable {N : ℕ} [NeZero N]

private theorem hpole_of_not_exists
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : ¬ ∃ a : A, ModularCurve.CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits) :
    ∀ a : A, P.ord (ModularCurve.CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a) ≤ 0 := by
  intro a
  by_contra hlt
  push Not at hlt
  rcases eq_or_ne (ModularCurve.CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a) 0 with h0 | h0
  · rw [h0] at hlt; simp at hlt
  · exact h ⟨a, (mem_nonunits_iff_ord_pos' P h0).mpr hlt⟩

private theorem exists_inv_sub_mem_nonunits
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (h : ¬ ∃ a : A, ModularCurve.CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits) :
    ∃ a : A, (ModularCurve.CharPModel.jBar N)⁻¹ -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits := by
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  have hsur : Function.Surjective (algebraMap (AlgebraicClosure ℚ) P.ResidueField) :=
    surjective_residueField_of_deg_eq_one' P (AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed P)
  by_cases hmem : ModularCurve.CharPModel.jBar N ∈ P.toValuationSubring
  · obtain ⟨c, hc⟩ := exists_hasValueAt' P hsur hmem
    have hcA : c ∉ A.toSubring := fun hcA => h ⟨⟨c, hcA⟩, hc⟩
    have hc0 : c ≠ 0 := fun h0 => hcA (h0 ▸ A.toSubring.zero_mem)
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    exact ⟨⟨c⁻¹, hcinv⟩, hc.inv' hc0⟩
  · have hinv : (ModularCurve.CharPModel.jBar N)⁻¹ ∈ P.toValuationSubring.nonunits :=
      (ValuationSubring.mem_nonunits_iff_or _).mpr (Or.inr (by simpa using hmem))
    refine ⟨0, ?_⟩
    simpa using hinv

end DichApp

end

end ModularCurve.CharPModel.SolINV

p2m_open "AlgebraicCurve~genus" in open  _root_.ModularCurve _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq.ModularCurve _root_.ModularCurve.CharPModel _root_.P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq.ModularCurve.CharPModel IsLocalRing in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (fm₁ fm₂ : ModularCurve.CharPModel.FibreModel N A ℓ (IsLocalRing.ResidueField A)
      (IsLocalRing.residue A))
    (cc₁ : fm₁.CuspChart) (cc₂ : fm₂.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularCurve.ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField A))
        (RatFunc (IsLocalRing.ResidueField A)))).Separable) :
    fm₁.spPlace Ideal.Quotient.mk_surjective dataAll hsep
      = fm₂.spPlace Ideal.Quotient.mk_surjective dataAll hsep := by
  classical
  have _ := cc₁
  have _ := cc₂
  obtain ⟨R, hspec, ⟨xj, hxjcoe, hxjres, hxjt, hfinj, hdegj, hFINj⟩,
      ⟨xinf, hxinfcoe, hxinfres, hxinft, hfini, hdegi, hINFi⟩⟩ :=
    SolINV.exists_RC_full' N ℓ A hℓN
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField A) N
  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    isCurveOver_modularFunctionFieldBar N
  have hxjbar : (xj : modularFunctionFieldBar N) = ModularCurve.CharPModel.jBar N := by
    rw [hxjcoe]; exact Subtype.ext rfl
  have hxinfbar : (xinf : modularFunctionFieldBar N) = (ModularCurve.CharPModel.jBar N)⁻¹ := by
    rw [hxinfcoe, hxjbar.symm, hxjcoe]
  funext P
  by_cases hPfin : ∃ a : A, ModularCurve.CharPModel.jBar N -
      algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits
  ·
    have hPfin' : ∃ a : A, (xj : modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits := by
      rw [hxjbar]; exact hPfin
    obtain ⟨Q₀, hQ₀, _⟩ := RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R xj hxjt hfinj hdegj hFINj P hPfin'
    have hcl : ∀ h : R.integers,
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          ({ModularCurve.CharPModel.jBar N} : Set (modularFunctionFieldBar N)))
          (h : modularFunctionFieldBar N) →
        ∀ a : A, (h : modularFunctionFieldBar N) -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) ∈
            Q₀.toValuationSubring.nonunits := by
      intro h hh a ha
      refine hQ₀ h ?_ a ha
      rw [SolINV.isIntegral_adjoin_singleton_congr' hxjbar]
      exact hh
    exact (FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits N ℓ A fm₁ dataAll hsep
        R hspec P hPfin Q₀ hcl).trans
      (FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits N ℓ A fm₂ dataAll hsep
        R hspec P hPfin Q₀ hcl).symm
  ·
    have hpole := SolINV.hpole_of_not_exists A P hPfin
    have hPinf' : ∃ a : A, (xinf : modularFunctionFieldBar N) -
        algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits := by
      rw [hxinfbar]; exact SolINV.exists_inv_sub_mem_nonunits A P hPfin
    obtain ⟨Q₀, hQ₀, _⟩ := RegularProlongation.existsUnique_place_forall_residue_sub_mem_nonunits
      A R xinf hxinft hfini hdegi hINFi P hPinf'
    have hcl : ∀ h : R.integers,
        IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
          ({(ModularCurve.CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
          (h : modularFunctionFieldBar N) →
        ∀ a : A, (h : modularFunctionFieldBar N) -
            algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A)
              (modularFunctionFieldC (ResidueField A) N) (IsLocalRing.residue A a) ∈
            Q₀.toValuationSubring.nonunits := by
      intro h hh a ha
      refine hQ₀ h ?_ a ha
      rw [SolINV.isIntegral_adjoin_singleton_congr' hxinfbar]
      exact hh
    exact (FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv N ℓ A fm₁ cc₁ dataAll hsep
        R hspec P hpole Q₀ hcl).trans
      (FibreModel.spPlace_eq_of_forall_residue_sub_mem_nonunits_jInv N ℓ A fm₂ cc₂ dataAll hsep
        R hspec P hpole Q₀ hcl).symm

end S_ModularCurve_CharPModel_FibreModel_spPlace_eq
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spPlace_eq (solution)
