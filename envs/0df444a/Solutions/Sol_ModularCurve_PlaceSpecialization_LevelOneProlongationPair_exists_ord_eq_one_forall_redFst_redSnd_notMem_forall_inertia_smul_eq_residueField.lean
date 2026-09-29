-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/297cdc03-ed4f-5fbf-8c55-e04c8bd6bf3d

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_LevelOneGlueData
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar
import Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_placeOfPoint_ne_placeInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue"
p2m_attr_erase "instance" "AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.LevelOnePhi.instAddCommGroup"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.PlaceSpecialization.ProlongationTuple.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.mk.sizeOf_spec ModularCurve.PlaceSpecialization.ProlongationTuple.residue₂_apply ModularCurve.PlaceSpecialization.ProlongationTuple.ExceptionalProlongations.mk.injEq ModularCurve.PlaceSpecialization.ProlongationTuple.residue₁_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero HahnSeries.ramScale_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace MOV1Core

section Bookkeeping

variable {α β : Type*}

private theorem mapDomain_apply_eq_sum [DecidableEq β] (E : α →₀ ℤ) (r : α → β) (v : β) :
    Finsupp.mapDomain r E v = ∑ W ∈ E.support, if r W = v then E W else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

private theorem mapDomain_nonneg (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) : 0 ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_nonneg fun W _ => by
    split_ifs with h'
    · exact h W h'
    · exact le_rfl

private theorem le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V : α} (hV : r V = v) :
    E V ≤ Finsupp.mapDomain r E v := by
  classical
  rw [mapDomain_apply_eq_sum]
  by_cases hs : V ∈ E.support
  · rw [← Finset.add_sum_erase _ _ hs, if_pos hV]
    refine le_add_of_nonneg_right (Finset.sum_nonneg fun W _ => ?_)
    split_ifs with h'
    · exact h W h'
    · exact le_rfl
  · rw [Finsupp.notMem_support_iff.mp hs]
    exact Finset.sum_nonneg fun W _ => by
      split_ifs with h'
      · exact h W h'
      · exact le_rfl

private theorem add_le_mapDomain (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, r W = v → 0 ≤ E W) {V V' : α} (hne : V ≠ V') (hV : r V = v) (hV' : r V' = v) :
    E V + E V' ≤ Finsupp.mapDomain r E v := by
  classical
  have hEV' : E V' = (E.erase V) V' := by rw [Finsupp.erase_ne (Ne.symm hne)]
  have herase : ∀ W, r W = v → 0 ≤ (E.erase V) W := by
    intro W hW
    by_cases hWV : W = V
    · rw [hWV, Finsupp.erase_same]
    · rw [Finsupp.erase_ne hWV]; exact h W hW
  have hsplit : Finsupp.mapDomain r E v = E V + Finsupp.mapDomain r (E.erase V) v := by
    conv_lhs => rw [← Finsupp.single_add_erase V E]
    rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.mapDomain_single, Finsupp.single_apply,
      if_pos hV]
  rw [hsplit, hEV']
  gcongr
  exact le_mapDomain (E.erase V) r v herase hV'

private theorem mapDomain_filter_nonneg (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) : 0 ≤ Finsupp.mapDomain r (D.filter p) v := by
  refine mapDomain_nonneg _ r v fun W hW => ?_
  rw [Finsupp.filter_apply]
  split_ifs with hp
  · exact h W hp hW
  · exact le_rfl

private theorem le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V : α} (hp : p V) (hV : r V = v) :
    D V ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  rw [hDV]
  refine le_mapDomain _ r v (fun W hW => ?_) hV
  rw [Finsupp.filter_apply]
  split_ifs with hp'
  · exact h W hp' hW
  · exact le_rfl

private theorem add_le_mapDomain_filter (D : α →₀ ℤ) (p : α → Prop) [DecidablePred p] (r : α → β) (v : β)
    (h : ∀ W, p W → r W = v → 0 ≤ D W) {V V' : α} (hne : V ≠ V')
    (hp : p V) (hV : r V = v) (hp' : p V') (hV' : r V' = v) :
    D V + D V' ≤ Finsupp.mapDomain r (D.filter p) v := by
  have hDV : D V = (D.filter p) V := by rw [Finsupp.filter_apply, if_pos hp]
  have hDV' : D V' = (D.filter p) V' := by rw [Finsupp.filter_apply, if_pos hp']
  rw [hDV, hDV']
  refine add_le_mapDomain _ r v (fun W hW => ?_) hne hV hV'
  rw [Finsupp.filter_apply]
  split_ifs with hp''
  · exact h W hp'' hW
  · exact le_rfl

private theorem mapDomain_eq_zero_of_forall_ne (E : α →₀ ℤ) (r : α → β) (v : β)
    (h : ∀ W, E W ≠ 0 → r W ≠ v) : Finsupp.mapDomain r E v = 0 := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_eq_zero fun W hW => if_neg (h W (Finsupp.mem_support_iff.mp hW))

private theorem sum_single_apply {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) [DecidableEq α] :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) W = ∑ i, if Q i = W then (1 : ℤ) else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.single_apply]

private theorem sum_single_apply_nonneg {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) :
    0 ≤ (∑ i, Finsupp.single (Q i) (1 : ℤ)) W := by
  classical
  rw [sum_single_apply]
  exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

private theorem sum_single_apply_eq_zero {ι : Type*} [Fintype ι] (Q : ι → α) (W : α) (h : ∀ i, Q i ≠ W) :
    (∑ i, Finsupp.single (Q i) (1 : ℤ)) W = 0 := by
  classical
  rw [sum_single_apply]
  exact Finset.sum_eq_zero fun i _ => if_neg (h i)

private theorem exists_of_sum_single_apply_ne_zero {ι : Type*} [Fintype ι] (Q : ι → α) (W : α)
    (h : (∑ i, Finsupp.single (Q i) (1 : ℤ)) W ≠ 0) : ∃ i, Q i = W := by
  by_contra hne
  push Not at hne
  exact h (sum_single_apply_eq_zero Q W hne)

end Bookkeeping

section PlaceValues

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem HasValue.sub {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

private theorem HasValue.sub_const {v : Place K F} {g : F} {a : K} (h : v.HasValue g a) (b : K) :
    v.HasValue (g - algebraMap K F b) (a - b) :=
  HasValue.sub h (v.hasValue_algebraMap b)

private theorem ord_pos_of_hasValue_zero (v : Place K F) {g : F} (hg : g ≠ 0) (h : v.HasValue g 0) :
    0 < v.ord g := by
  have hmem := h.mem
  have hres : IsLocalRing.residue v.toValuationSubring ⟨g, hmem⟩ = 0 := by
    rw [h.residue_eq, map_zero]
  have hmax : (⟨g, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres
  have h0 : 0 ≤ v.ord g := v.ord_nonneg_of_mem hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax hu

private theorem hasValue_of_ord_sub_pos (v : Place K F) {g : F} {b : K}
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hmax : (⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hgmem : g ∈ v.toValuationSubring := by
    have : g = (g - algebraMap K F b) + algebraMap K F b := by ring
    rw [this]
    exact add_mem hmem (v.algebraMap_mem' b)
  refine ⟨hgmem, ?_⟩
  have hx : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨_, hmem⟩ + ⟨algebraMap K F b, v.algebraMap_mem' b⟩ := Subtype.ext (by push_cast; ring)
  rw [hx, map_add, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, zero_add]
  exact v.residue_algebraMap b

private theorem ord_sub_eq_zero_of_hasValue_ne (v : Place K F) {g : F} {a b : K}
    (h : v.HasValue g a) (hab : a ≠ b) : v.ord (g - algebraMap K F b) = 0 :=
  (HasValue.sub_const h b).ord_eq_zero (sub_ne_zero.mpr hab)

private theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {b : K}
    (h : v.HasValue g b) (hne : g - algebraMap K F b ≠ 0) : 0 < v.ord (g - algebraMap K F b) := by
  have h' := HasValue.sub_const h b
  rw [sub_self] at h'
  exact ord_pos_of_hasValue_zero v hne h'

private theorem eq_of_ord_sub_pos_of_hasValue (v : Place K F) {g : F} {a b : K}
    (ha : v.HasValue g a) (h : 0 < v.ord (g - algebraMap K F b)) : b = a :=
  (hasValue_of_ord_sub_pos v h).unique ha

private theorem ord_sub_const_nonneg (v : Place K F) {g : F} (hg : g = 0 ∨ 0 ≤ v.ord g) (b : K) :
    0 ≤ v.ord (g - algebraMap K F b) := by
  have hmem : g ∈ v.toValuationSubring := by
    rcases hg with rfl | hg
    · exact zero_mem _
    · by_cases h0 : g = 0
      · rw [h0]; exact zero_mem _
      · exact v.mem_of_ord_nonneg h0 hg
  exact v.ord_nonneg_of_mem (sub_mem hmem (v.algebraMap_mem' b))

private theorem ord_nonneg_of_mem_riemannRochSpace {D : Divisor K F} {g : F} (hg : g ∈ riemannRochSpace D)
    (v : Place K F) (hv : D v = 0) : g = 0 ∨ 0 ≤ v.ord g := by
  have h := (mem_riemannRochSpace_iff.mp hg) v
  rw [hv, neg_zero] at h
  exact h

private theorem riemannRochSpace_mono {D D' : Divisor K F} (h : ∀ v, D v ≤ D' v) :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro g hg
  rw [mem_riemannRochSpace_iff] at hg ⊢
  intro v
  rcases hg v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h v)) h1)

private theorem ord_neg_of_ord_sub_const_neg (v : Place K F) {g : F} {b : K}
    (h : v.ord (g - algebraMap K F b) < 0) : g ≠ 0 ∧ v.ord g < 0 := by
  by_contra hc
  have : g = 0 ∨ 0 ≤ v.ord g := by
    by_cases h0 : g = 0
    · exact Or.inl h0
    · exact Or.inr (not_lt.mp fun hlt => hc ⟨h0, hlt⟩)
  exact absurd (ord_sub_const_nonneg v this b) (not_le.mpr h)

private theorem surjective_algebraMap_residueField [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    Function.Surjective (algebraMap K v.ResidueField) := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

private theorem exists_hasValue_of_ord_nonneg [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) {g : F}
    (hg : g = 0 ∨ 0 ≤ v.ord g) : ∃ a : K, v.HasValue g a := by
  have hmem : g ∈ v.toValuationSubring := by
    rcases hg with rfl | hg
    · exact zero_mem _
    · by_cases h0 : g = 0
      · rw [h0]; exact zero_mem _
      · exact v.mem_of_ord_nonneg h0 hg
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective (surjective_algebraMap_residueField v) hmem
  exact ⟨a, ha⟩

private theorem ord_const_mul (v : Place K F) {c : K} (hc : c ≠ 0) (g : F) :
    v.ord (algebraMap K F c * g) = v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [mul_zero]
  · rw [v.ord_mul ((map_ne_zero _).mpr hc) hg]
    have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
      (v.hasValue_algebraMap c).isUnit hc
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (algebraMap K F c) = 0 at h0
    rw [h0, zero_add]

private theorem degree_sum_single [IsAlgClosed K] [IsCurveOver K F] {ι : Type*} [Fintype ι] (Q : ι → Place K F) :
    Divisor.degree (∑ i, Finsupp.single (Q i) (1 : ℤ)) = Fintype.card ι := by
  rw [map_sum]
  simp_rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed]
  simp

open scoped Pointwise in

theorem hasValue_smul_semilinear {K F : Type*} [Field K] [Field F] [Algebra K F] (g : SemilinearAut K F)
    {v : Place K F} {G : F} {c : K} (hc : v.HasValue G c) :
    (g • v).HasValue (g • G) (SemilinearAut.baseAut g c) := by
  obtain ⟨h, hres⟩ := hc
  refine ⟨ValuationSubring.smul_mem_pointwise_smul g G v.toValuationSubring h, ?_⟩
  have hx : (⟨g • G, ValuationSubring.smul_mem_pointwise_smul g G v.toValuationSubring h⟩ :
      (g • v).toValuationSubring) = SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨G, h⟩ := by
    ext; rfl
  have key : SemilinearAut.smulResidueRingEquiv g v (IsLocalRing.residue _ ⟨G, h⟩)
      = IsLocalRing.residue _ (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨G, h⟩) := by
    show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    rfl
  rw [hx]
  show IsLocalRing.residue ↥(g • v.toValuationSubring)
      (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨G, h⟩) =
    algebraMap K (g • v).ResidueField (SemilinearAut.baseAut g c)
  rw [← key, hres, SemilinearAut.smulResidueRingEquiv_algebraMap]

end PlaceValues

section Seam

private theorem fullC_one_eq (K : Type*) [Field K] :
    modularFunctionFieldFullC K 1 = modularFunctionFieldC K 1 := by
  refine le_antisymm ?_ (modularFunctionFieldC_le_full K 1)
  rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  haveI := hne
  obtain rfl : d = 1 := Nat.dvd_one.mp hdvd
  rw [qExpand_one_apply]
  exact jqModC_mem K 1

private theorem mem_fullC_one (K : Type*) [Field K] (g : ↥(modularFunctionFieldC K 1)) :
    (g : LaurentSeries K) ∈ modularFunctionFieldFullC K 1 := by
  rw [fullC_one_eq]; exact g.2

private def toFull (K : Type*) [Field K] (g : ↥(modularFunctionFieldC K 1)) : ↥(modularFunctionFieldFullC K 1) :=
  ⟨(g : LaurentSeries K), mem_fullC_one K g⟩

@[scoped simp] private theorem coe_toFull (K : Type*) [Field K] (g : ↥(modularFunctionFieldC K 1)) :
    ((toFull K g : ↥(modularFunctionFieldFullC K 1)) : LaurentSeries K) = (g : LaurentSeries K) :=
  Subtype.coe_mk _ (mem_fullC_one K g)

private theorem residue_inv_eq_zero_of_not_mem {A : ValuationSubring (AlgebraicClosure ℚ)} {c : AlgebraicClosure ℚ} (hc : c ∉ A) (hc' : c⁻¹ ∈ A) :
    IsLocalRing.residue A ⟨c⁻¹, hc'⟩ = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  apply hc
  have hc0 : c ≠ 0 := fun h0 => hc (h0 ▸ A.zero_mem)
  have h1 : c⁻¹ * (w : AlgebraicClosure ℚ) = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have : (w : AlgebraicClosure ℚ) = c := by
    calc (w : AlgebraicClosure ℚ) = c * (c⁻¹ * w) := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
      _ = c := by rw [h1, mul_one]
  rw [← this]
  exact w.2

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField A) q]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
  (R : P.LevelOneProlongationPair)

private theorem redBar_eq_id : R.redBar = RingHom.id (ResidueField A) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  exact R.redBar_residue a

private theorem coe_ι (g : ↥(modularFunctionFieldFullC (ResidueField A) 1)) :
    ((R.ι g : ↥(modularFunctionFieldC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      (g : LaurentSeries (ResidueField A)) := by
  rw [R.ι_coe g, redBar_eq_id R, coeffMap_id]

private theorem ι_toFull (g : ↥(modularFunctionFieldC (ResidueField A) 1)) :
    R.ι (toFull (ResidueField A) g) = g :=
  Subtype.ext (by rw [coe_ι, coe_toFull])

private theorem toFull_ι (g : ↥(modularFunctionFieldFullC (ResidueField A) 1)) :
    toFull (ResidueField A) (R.ι g) = g :=
  Subtype.ext (by rw [coe_toFull, coe_ι])

private theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) c) =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1) c := by
  apply Subtype.ext
  rw [coe_ι]

  have h₁ : ((algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) c :
      ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c := rfl
  have h₂ : ((algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1) c :
      ↥(modularFunctionFieldC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) =
      algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c := rfl
  rw [h₁, h₂]

private theorem algebraMap_mem_integers₁ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers :=
  (R.R₁.algebraMap_mem_iff a).mpr a.2

private theorem algebraMap_mem_integers₂ (a : A) :
    algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers :=
  (R.R₂.algebraMap_mem_iff a).mpr a.2

private theorem residue₁_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1) (IsLocalRing.residue A a) := by
  rw [LevelOneProlongationPair.residue₁_apply, ← ι_algebraMap R]
  congr 1
  exact R.R₁.residue_algebraMap a

private theorem residue₂_algebraMap (a : A)
    (h : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h⟩ =
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1) (IsLocalRing.residue A a) := by
  rw [LevelOneProlongationPair.residue₂_apply, ← ι_algebraMap R]
  congr 1
  exact R.R₂.residue_algebraMap a

private theorem residue₁_sub_algebraMap (f : ↥(modularFunctionFieldBar (1 * q))) (h : f ∈ R.R₁.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = R.residue₁ ⟨f, h⟩ -
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1) (IsLocalRing.residue A a) := by
  rw [← residue₁_algebraMap R a (algebraMap_mem_integers₁ R a), ← map_sub]
  rfl

private theorem residue₂_sub_algebraMap (f : ↥(modularFunctionFieldBar (1 * q))) (h : f ∈ R.R₂.integers) (a : A)
    (h' : f - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = R.residue₂ ⟨f, h⟩ -
      algebraMap (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1) (IsLocalRing.residue A a) := by
  rw [← residue₂_algebraMap R a (algebraMap_mem_integers₂ R a), ← map_sub]
  rfl

private theorem residue₁_one_sub_smul (f : ↥(modularFunctionFieldBar (1 * q))) (h : f ∈ R.R₁.integers) (a : A)
    (ha : IsLocalRing.residue A a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₁.integers) :
    R.residue₁ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₁.integers) = 1 - ⟨_, algebraMap_mem_integers₁ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₁_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

private theorem residue₂_one_sub_smul (f : ↥(modularFunctionFieldBar (1 * q))) (h : f ∈ R.R₂.integers) (a : A)
    (ha : IsLocalRing.residue A a = 0)
    (h' : 1 - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) * f ∈ R.R₂.integers) :
    R.residue₂ ⟨_, h'⟩ = 1 := by
  have hx : (⟨_, h'⟩ : R.R₂.integers) = 1 - ⟨_, algebraMap_mem_integers₂ R a⟩ * ⟨f, h⟩ := rfl
  rw [hx, map_sub, map_one, map_mul, residue₂_algebraMap R a, ha, map_zero, zero_mul, sub_zero]

private theorem residue_ne_zero_iff₁ (x : R.R₁.integers) : R.residue₁ x ≠ 0 ↔ R.R₁.residue x ≠ 0 := by
  rw [LevelOneProlongationPair.residue₁_apply]
  exact map_ne_zero_iff R.ι R.ι.injective

private theorem residue_ne_zero_iff₂ (x : R.R₂.integers) : R.residue₂ x ≠ 0 ↔ R.R₂.residue x ≠ 0 := by
  rw [LevelOneProlongationPair.residue₂_apply]
  exact map_ne_zero_iff R.ι R.ι.injective

end Seam

section Geometry

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

private theorem infty_def [DecidableEq (RatFunc k)] :
    P.redFst (cuspInftyBar (1 * q)) = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) :=
  redFst_cuspInftyBar P

private theorem redSnd_cuspZeroBar_eq [DecidableEq (RatFunc k)] :
    P.redSnd (cuspZeroBar (1 * q)) = P.redFst (cuspInftyBar (1 * q)) := by
  rw [redFst_cuspInftyBar P]; exact redSnd_cuspZeroBar P

private theorem frob_infty [DecidableEq (RatFunc k)] :
    frobOnPlacesGeomLevel k 1 data hKr (P.redFst (cuspInftyBar (1 * q))) = P.redFst (cuspInftyBar (1 * q)) := by
  rw [redFst_cuspInftyBar P, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty]

private theorem frob_frob_infty [DecidableEq (RatFunc k)] :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst (cuspInftyBar (1 * q)))) =
      P.redFst (cuspInftyBar (1 * q)) := by
  rw [frob_infty P, frob_infty P]

private theorem eq_infty_of_frob_eq_infty [DecidableEq (RatFunc k)] {v : Place k ↥(modularFunctionFieldC k 1)}
    (h : frobOnPlacesGeomLevel k 1 data hKr v = P.redFst (cuspInftyBar (1 * q))) :
    v = P.redFst (cuspInftyBar (1 * q)) :=
  ModularCurve.frobOnPlacesGeomLevel_injective k 1 data hKr (h.trans (frob_infty P).symm)

private theorem trichotomy (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W ∨
      (frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W)) = P.redFst W ∧
        P.redSnd W = frobOnPlacesGeomLevel k 1 data hKr (P.redFst W)) := by
  have hφinj := ModularCurve.frobOnPlacesGeomLevel_injective k 1 data hKr
  rcases P.d1 W with h | h
  ·
    change P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) at h
    by_cases hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W)) = P.redSnd W
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [h, hfix]
      · rw [h, hfix]
    · exact Or.inr (Or.inl ⟨h, hfix⟩)
  ·
    change frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W at h
    by_cases hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W)) = P.redFst W
    · exact Or.inr (Or.inr ⟨hfix, h.symm⟩)
    · exact Or.inl ⟨h, hfix⟩

private theorem not_fixed_redFst_of_isStrictTypeOne {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeOne W) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W)) ≠ P.redFst W := h.2

private theorem not_fixed_redSnd_of_isStrictTypeOne {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeOne W) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W)) ≠ P.redSnd W := by
  intro hfix; apply h.2; rw [← h.1] at hfix
  exact ModularCurve.frobOnPlacesGeomLevel_injective k 1 data hKr hfix

private theorem not_fixed_redSnd_of_isStrictTypeTwo {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeTwo W) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W)) ≠ P.redSnd W := h.2

private theorem not_fixed_redFst_of_isStrictTypeTwo {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeTwo W) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.redFst W)) ≠ P.redFst W := by
  intro hfix; apply h.2; rw [h.1] at hfix
  exact ModularCurve.frobOnPlacesGeomLevel_injective k 1 data hKr hfix

private theorem not_isStrictTypeTwo_of_isStrictTypeOne {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeOne W) : ¬ P.IsStrictTypeTwo W := by
  intro h2
  apply h2.2
  have := h.1
  rw [h2.1] at this
  exact this

private theorem redFst_ne_infty_of_strict [DecidableEq (RatFunc k)] {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W) : P.redFst W ≠ P.redFst (cuspInftyBar (1 * q)) := by
  intro heq
  rcases h with h | h
  · exact not_fixed_redFst_of_isStrictTypeOne P h (by rw [heq, frob_frob_infty P])
  · exact not_fixed_redFst_of_isStrictTypeTwo P h (by rw [heq, frob_frob_infty P])

private theorem redSnd_ne_infty_of_strict [DecidableEq (RatFunc k)] {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W) : P.redSnd W ≠ P.redFst (cuspInftyBar (1 * q)) := by
  intro heq
  rcases h with h | h
  · exact not_fixed_redSnd_of_isStrictTypeOne P h (by rw [heq, frob_frob_infty P])
  · exact not_fixed_redSnd_of_isStrictTypeTwo P h (by rw [heq, frob_frob_infty P])

private theorem heckeAlphaBar_j :
    heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jFun (q := q) :=
  Subtype.ext (coe_heckeAlphaBar 1 q _)

private theorem redFst_ne_infty_of_not_isCuspidal [DecidableEq (RatFunc k)]
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))} (h : ¬ P.IsCuspidal W) :
    P.redFst W ≠ P.redFst (cuspInftyBar (1 * q)) := by
  unfold PlaceSpecialization.IsCuspidal at h
  push Not at h
  obtain ⟨b, hb⟩ := h
  have hb' := hb
  rw [← heckeAlphaBar_j] at hb'
  rw [redFst_eq_charLGeomPlaceOfPoint_of_ord_pos P W b hb', redFst_cuspInftyBar P]
  intro heq
  unfold charLGeomPlaceOfPoint at heq
  exact RationalFunctionField.placeOfPoint_ne_placeInfty k (red b) ((charLGeomPlaceEquiv k).injective heq)

private theorem isCuspidal_of_redFst_eq_infty [DecidableEq (RatFunc k)]
    {W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (h : P.redFst W = P.redFst (cuspInftyBar (1 * q))) : P.IsCuspidal W := by
  by_contra hc
  exact redFst_ne_infty_of_not_isCuspidal P hc h

private theorem charLGeomPlaceOfPoint_mem_ssPlaces [DecidableEq k] {a : k} (ha : a ∈ ssJSet q k) :
    charLGeomPlaceOfPoint k a ∈ ssPlaces q 1 k :=
  (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr ⟨a, ha, rfl⟩

private theorem frob_mem_ssPlaces_iff [DecidableEq k] [IsAlgClosed k] (v : Place k ↥(modularFunctionFieldC k 1)) :
    frobOnPlacesGeomLevel k 1 data hKr v ∈ ssPlaces q 1 k ↔ v ∈ ssPlaces q 1 k := by
  haveI : PerfectField k := inferInstance
  constructor
  · intro h
    obtain ⟨a, ha, hav⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
    obtain ⟨b, rfl⟩ := IsAlgClosed.exists_pow_nat_eq a (Fact.out : q.Prime).pos
    rw [← ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr b] at hav
    have hv := ModularCurve.frobOnPlacesGeomLevel_injective k 1 data hKr hav
    rw [← hv]
    exact charLGeomPlaceOfPoint_mem_ssPlaces ((ModularCurve.pow_mem_ssJSet_iff_of_perfectField q b).mp ha)
  · intro h
    obtain ⟨a, ha, rfl⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
    rw [ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
    exact charLGeomPlaceOfPoint_mem_ssPlaces ((ModularCurve.pow_mem_ssJSet_iff_of_perfectField q a).mpr ha)

private theorem frobNodePair_fst_mem_ssPlaces [DecidableEq k] {a : k} (ha : a ∈ ssJSet q k) :
    (frobNodePair q a).1 ∈ ssPlaces q 1 k := by
  rw [frobNodePair_fst]; exact charLGeomPlaceOfPoint_mem_ssPlaces ha

private theorem frobNodePair_snd_mem_ssPlaces [DecidableEq k] [IsAlgClosed k] {a : k} (ha : a ∈ ssJSet q k) :
    (frobNodePair q a).2 ∈ ssPlaces q 1 k := by
  haveI : PerfectField k := inferInstance
  rw [frobNodePair_snd]
  exact charLGeomPlaceOfPoint_mem_ssPlaces ((ModularCurve.pow_mem_ssJSet_iff_of_perfectField q a).mpr ha)

private theorem fixed_of_mem_ssPlaces [DecidableEq k] [IsAlgClosed k] {v : Place k ↥(modularFunctionFieldC k 1)}
    (hv : v ∈ ssPlaces q 1 k) :
    frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v := by
  obtain ⟨a, ha, rfl⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp hv
  rw [ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint,
    ← pow_mul, ← pow_two, ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha]

end Geometry

section Count

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

private theorem one_le_sum_single_apply_self {α ι : Type*} [Fintype ι] (Q : ι → α) (i : ι) :
    1 ≤ (∑ j, Finsupp.single (Q j) (1 : ℤ)) (Q i) := by
  classical
  rw [sum_single_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), if_pos rfl]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num)

private theorem ord_algebraMap_eq_zero {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, Place.ord_zero]
  · exact (v.hasValue_algebraMap c).ord_eq_zero hc

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr
set_option hygiene false in
local notation "∞̃" => P.redFst (cuspInftyBar (1 * q))

variable (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

private theorem kind (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeOne V ∨ P.IsStrictTypeTwo V ∨
    (φ (φ (P.redFst V)) = P.redFst V ∧ P.redFst V ≠ ∞̃ ∧ P.redSnd V = φ (P.redFst V)) ∨
    (P.IsInftySide V ∧ P.redFst V = ∞̃ ∧ P.redSnd V = ∞̃) ∨
    (P.IsZeroSide V ∧ P.redFst V = ∞̃ ∧ P.redSnd V = ∞̃) := by
  classical
  rcases trichotomy P V with h | h | ⟨hfix, hsnd⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · by_cases hinf : P.redFst V = ∞̃
    · have hsnd' : P.redSnd V = ∞̃ := by rw [hsnd, hinf, frob_infty P]
      rcases ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal P V
          (isCuspidal_of_redFst_eq_infty P hinf) with hs | hs
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hs, hinf, hsnd'⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hs, hinf, hsnd'⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hfix, hinf, hsnd⟩))

variable {P}

private theorem nonneg_typeOne_fibre {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {Z : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    {v : Place k ↥(modularFunctionFieldC k 1)} (hv : v ∈ Z) :
    ∀ W, P.IsStrictTypeOne W → P.redFst W = v → 0 ≤ D W := by
  intro W h1 hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨-, hZ⟩ | ⟨h2, -⟩
  · exact hZ (by rw [hW]; exact hv)
  · exact not_isStrictTypeTwo_of_isStrictTypeOne P h1 h2

private theorem nonneg_typeTwo_fibre {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {Z : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    {v : Place k ↥(modularFunctionFieldC k 1)} (hv : v ∈ Z) :
    ∀ W, P.IsStrictTypeTwo W → P.redSnd W = v → 0 ≤ D W := by
  intro W h2 hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨-, hZ⟩
  · exact not_isStrictTypeTwo_of_isStrictTypeOne P h1 h2
  · exact hZ (by rw [hW]; exact hv)

private theorem nonneg_fixed_fibre {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {Z : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    {v : Place k ↥(modularFunctionFieldC k 1)} (hv : φ (φ v) = v) :
    ∀ W, P.redFst W = v → 0 ≤ D W := by
  intro W hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨h2, -⟩
  · exact not_fixed_redFst_of_isStrictTypeOne P h1 (by rw [hW]; exact hv)
  · exact not_fixed_redFst_of_isStrictTypeTwo P h2 (by rw [hW]; exact hv)

private theorem nonneg_infty_fibre {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {Z : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z)) :
    ∀ W, P.IsInftySide W → P.redFst W = ∞̃ → 0 ≤ D W := by
  classical
  intro W _ hW
  by_contra hlt
  push Not at hlt
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨h2, -⟩
  · exact redFst_ne_infty_of_strict P (Or.inl h1) hW
  · exact redFst_ne_infty_of_strict P (Or.inr h2) hW

private theorem nonneg_zero_fibre {D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    {Z : Finset (Place k ↥(modularFunctionFieldC k 1))}
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z)) :
    ∀ W, P.IsZeroSide W → P.redSnd W = P.redSnd (cuspZeroBar (1 * q)) → 0 ≤ D W := by
  classical
  intro W _ hW
  by_contra hlt
  push Not at hlt
  rw [redSnd_cuspZeroBar_eq P] at hW
  rcases hDpole W hlt with ⟨h1, -⟩ | ⟨h2, -⟩
  · exact redSnd_ne_infty_of_strict P (Or.inl h1) hW
  · exact redSnd_ne_infty_of_strict P (Or.inr h2) hW

private theorem rawResidue₁_ne_zero (R : P.LevelOneProlongationPair) {x : R.R₁.integers} (h : R.residue₁ x ≠ 0) :
    R.R₁.residue x ≠ 0 := by
  intro h0; apply h; rw [LevelOneProlongationPair.residue₁_apply, h0, map_zero]

private theorem rawResidue₂_ne_zero (R : P.LevelOneProlongationPair) {x : R.R₂.integers} (h : R.residue₂ x ≠ 0) :
    R.R₂.residue x ≠ 0 := by
  intro h0; apply h; rw [LevelOneProlongationPair.residue₂_apply, h0, map_zero]

private theorem classBound (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (Z : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hz₁ : P.redFst V ∈ Z) (hz₂ : P.redSnd V ∈ Z) :
    (P.IsStrictTypeOne V ∧
      D V ≤ (P.redFst V).ord (R.residue₁ ⟨f, h₁⟩) ∧
      ∀ V', V' ≠ V → P.IsStrictTypeOne V' → P.redFst V' = P.redFst V →
        D V + D V' ≤ (P.redFst V).ord (R.residue₁ ⟨f, h₁⟩)) ∨
    (P.IsStrictTypeTwo V ∧
      D V ≤ (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.IsStrictTypeTwo V' → P.redSnd V' = P.redSnd V →
        D V + D V' ≤ (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩)) ∨
    ((φ (φ (P.redFst V)) = P.redFst V ∧ P.redFst V ≠ ∞̃ ∧ P.redSnd V = φ (P.redFst V)) ∧
      D V ≤ (P.redFst V).ord (R.residue₁ ⟨f, h₁⟩) + (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.redFst V' = P.redFst V →
        D V + D V' ≤ (P.redFst V).ord (R.residue₁ ⟨f, h₁⟩) + (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩)) ∨
    ((P.IsInftySide V ∧ P.redFst V = ∞̃ ∧ P.redSnd V = ∞̃) ∧
      D V ≤ (P.redFst V).ord (R.residue₁ ⟨f, h₁⟩) ∧
      ∀ V', V' ≠ V → P.IsInftySide V' → P.redFst V' = ∞̃ →
        D V + D V' ≤ (P.redFst V).ord (R.residue₁ ⟨f, h₁⟩)) ∨
    ((P.IsZeroSide V ∧ P.redFst V = ∞̃ ∧ P.redSnd V = ∞̃) ∧
      D V ≤ (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩) ∧
      ∀ V', V' ≠ V → P.IsZeroSide V' → P.redSnd V' = ∞̃ →
        D V + D V' ≤ (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩)) := by
  classical
  obtain ⟨hDF, hDS, hCI, hCZ⟩ :
      R.DivisorLawFst ∧ R.DivisorLawSnd ∧ R.CuspLawInfty ∧ R.CuspLawZero := hR
  have hf₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := rawResidue₁_ne_zero R hf₁
  have hf₂' : R.R₂.residue ⟨f, h₂⟩ ≠ 0 := rawResidue₂_ne_zero R hf₂
  rcases kind P V with hk | hk | hk | hk | hk
  ·
    have hlaw := hDF f h₁ h₂ hf₁' hf₂' D hD (P.redFst V) hk.2
    refine Or.inl ⟨hk, ?_, ?_⟩
    · rw [← hlaw]
      exact le_mapDomain_filter D P.IsStrictTypeOne P.redFst _
        (nonneg_typeOne_fibre hDpole hz₁) hk rfl
    · intro V' hne h1' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D P.IsStrictTypeOne P.redFst _
        (nonneg_typeOne_fibre hDpole hz₁) (Ne.symm hne) hk rfl h1' hV'
  ·
    have hlaw := hDS f h₁ h₂ hf₁' hf₂' D hD (P.redSnd V) hk.2
    refine Or.inr (Or.inl ⟨hk, ?_, ?_⟩)
    · rw [← hlaw]
      exact le_mapDomain_filter D P.IsStrictTypeTwo P.redSnd _
        (nonneg_typeTwo_fibre hDpole hz₂) hk rfl
    · intro V' hne h2' hV'
      rw [← hlaw]
      exact add_le_mapDomain_filter D P.IsStrictTypeTwo P.redSnd _
        (nonneg_typeTwo_fibre hDpole hz₂) (Ne.symm hne) hk rfl h2' hV'
  ·
    obtain ⟨hfix, hninf, hsnd⟩ := hk
    have hlaw := hO f h₁ h₂ hf₁' hf₂' D hD (P.redFst V) hfix hninf
    refine Or.inr (Or.inr (Or.inl ⟨⟨hfix, hninf, hsnd⟩, ?_, ?_⟩))
    · rw [hsnd, ← hlaw]
      exact le_mapDomain D P.redFst _ (nonneg_fixed_fibre hDpole hfix) rfl
    · intro V' hne hV'
      rw [hsnd, ← hlaw]
      exact add_le_mapDomain D P.redFst _ (nonneg_fixed_fibre hDpole hfix) (Ne.symm hne) rfl hV'
  ·
    obtain ⟨hs, hinf, hsnd⟩ := hk
    have hlaw := hCI f h₁ h₂ hf₁' hf₂' D hD
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨hs, hinf, hsnd⟩, ?_, ?_⟩)))
    · rw [hinf, ← hlaw]
      exact le_mapDomain_filter D P.IsInftySide P.redFst _ (nonneg_infty_fibre hDpole) hs hinf
    · intro V' hne hs' hV'
      rw [hinf, ← hlaw]
      exact add_le_mapDomain_filter D P.IsInftySide P.redFst _ (nonneg_infty_fibre hDpole)
        (Ne.symm hne) hs hinf hs' hV'
  ·
    obtain ⟨hs, hinf, hsnd⟩ := hk
    have hlaw := hCZ f h₁ h₂ hf₁' hf₂' D hD
    have h0 : P.redSnd (cuspZeroBar (1 * q)) = ∞̃ := redSnd_cuspZeroBar_eq P
    have hsnd' : P.redSnd V = P.redSnd (cuspZeroBar (1 * q)) := by rw [hsnd, h0]
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨hs, hinf, hsnd⟩, ?_, ?_⟩)))
    · rw [hsnd', ← hlaw]
      exact le_mapDomain_filter D P.IsZeroSide P.redSnd _ (nonneg_zero_fibre hDpole) hs hsnd'
    · intro V' hne hs' hV'
      rw [hsnd', ← hlaw]
      exact add_le_mapDomain_filter D P.IsZeroSide P.redSnd _ (nonneg_zero_fibre hDpole)
        (Ne.symm hne) hs hsnd' hs' (by rw [hV', h0])

private theorem one_le_ord_residue_or (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (Z : Finset (Place k ↥(modularFunctionFieldC k 1)))
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDV₀ : 1 ≤ D V₀)
    (hd₁ : P.redFst V₀ ∈ Z) (hd₂ : P.redSnd V₀ ∈ Z)
    (hreg₁ : 0 ≤ (P.redFst V₀).ord (R.residue₁ ⟨f, h₁⟩))
    (hreg₂ : 0 ≤ (P.redSnd V₀).ord (R.residue₂ ⟨f, h₂⟩)) :
    1 ≤ (P.redFst V₀).ord (R.residue₁ ⟨f, h₁⟩) ∨ 1 ≤ (P.redSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) := by
  rcases classBound R hR hO f h₁ h₂ hf₁ hf₂ D hD Z hDpole V₀ hd₁ hd₂ with
    ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩
  · exact Or.inl (hDV₀.trans hb)
  · exact Or.inr (hDV₀.trans hb)
  · rcases le_or_gt 1 ((P.redFst V₀).ord (R.residue₁ ⟨f, h₁⟩)) with h | h
    · exact Or.inl h
    · right; omega
  · exact Or.inl (hDV₀.trans hb)
  · exact Or.inr (hDV₀.trans hb)

private theorem eq_one_and_forall_of_orders (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (hf₁ : R.residue₁ ⟨f, h₁⟩ ≠ 0) (hf₂ : R.residue₂ ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (Z : Finset (Place k ↥(modularFunctionFieldC k 1))) (hZinf : ∞̃ ∈ Z)
    (hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hDV₀ : 1 ≤ D V₀)
    (hd₁ : P.redFst V₀ ∈ Z) (hd₂ : P.redSnd V₀ ∈ Z)
    (p₁ p₂ : Prop) (hp : ¬ (p₁ ∧ p₂))
    (hZ₁ : ∀ z ∈ Z, z ≠ P.redFst V₀ → z.ord (R.residue₁ ⟨f, h₁⟩) = 0)
    (hZ₂ : ∀ z ∈ Z, z ≠ P.redSnd V₀ → z.ord (R.residue₂ ⟨f, h₂⟩) = 0)
    (h1p : p₁ → (P.redFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 1)
    (h1n : ¬ p₁ → (P.redFst V₀).ord (R.residue₁ ⟨f, h₁⟩) = 0)
    (h2p : p₂ → (P.redSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 1)
    (h2n : ¬ p₂ → (P.redSnd V₀).ord (R.residue₂ ⟨f, h₂⟩) = 0) :
    D V₀ = 1 ∧ ∀ V, V ≠ V₀ → 1 ≤ D V → P.redFst V ∈ Z → P.redSnd V ∈ Z → False := by
  classical
  have hφinj := ModularCurve.frobOnPlacesGeomLevel_injective k 1 data hKr

  have hA : ∀ z ∈ Z, 0 ≤ z.ord (R.residue₁ ⟨f, h₁⟩) ∧ z.ord (R.residue₁ ⟨f, h₁⟩) ≤ 1 ∧
      (1 ≤ z.ord (R.residue₁ ⟨f, h₁⟩) → z = P.redFst V₀ ∧ p₁) := by
    intro z hz
    by_cases hzd : z = P.redFst V₀
    · by_cases hq : p₁
      · rw [hzd, h1p hq]; exact ⟨by norm_num, le_rfl, fun _ => ⟨rfl, hq⟩⟩
      · rw [hzd, h1n hq]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩
    · rw [hZ₁ z hz hzd]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩
  have hB : ∀ z ∈ Z, 0 ≤ z.ord (R.residue₂ ⟨f, h₂⟩) ∧ z.ord (R.residue₂ ⟨f, h₂⟩) ≤ 1 ∧
      (1 ≤ z.ord (R.residue₂ ⟨f, h₂⟩) → z = P.redSnd V₀ ∧ p₂) := by
    intro z hz
    by_cases hzd : z = P.redSnd V₀
    · by_cases hq : p₂
      · rw [hzd, h2p hq]; exact ⟨by norm_num, le_rfl, fun _ => ⟨rfl, hq⟩⟩
      · rw [hzd, h2n hq]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩
    · rw [hZ₂ z hz hzd]; exact ⟨le_rfl, by norm_num, fun h => absurd h (by norm_num)⟩

  have hloc : ∀ V, P.redFst V ∈ Z → P.redSnd V ∈ Z → 1 ≤ D V →
      (p₁ ∧ (
        (P.IsStrictTypeOne V ∧ P.redFst V = P.redFst V₀ ∧
          ∀ V', V' ≠ V → P.IsStrictTypeOne V' → P.redFst V' = P.redFst V → D V + D V' ≤ 1) ∨
        (φ (φ (P.redFst V)) = P.redFst V ∧ P.redFst V ≠ ∞̃ ∧ P.redFst V = P.redFst V₀ ∧
          ∀ V', V' ≠ V → P.redFst V' = P.redFst V → D V + D V' ≤ 1) ∨
        (P.IsInftySide V ∧ P.redFst V = ∞̃ ∧ ∞̃ = P.redFst V₀ ∧
          ∀ V', V' ≠ V → P.IsInftySide V' → P.redFst V' = ∞̃ → D V + D V' ≤ 1))) ∨
      (p₂ ∧ (
        (P.IsStrictTypeTwo V ∧ P.redSnd V = P.redSnd V₀ ∧
          ∀ V', V' ≠ V → P.IsStrictTypeTwo V' → P.redSnd V' = P.redSnd V → D V + D V' ≤ 1) ∨
        (φ (φ (P.redFst V)) = P.redFst V ∧ P.redFst V ≠ ∞̃ ∧ φ (P.redFst V) = P.redSnd V₀ ∧
          ∀ V', V' ≠ V → P.redFst V' = P.redFst V → D V + D V' ≤ 1) ∨
        (P.IsZeroSide V ∧ P.redSnd V = ∞̃ ∧ ∞̃ = P.redSnd V₀ ∧
          ∀ V', V' ≠ V → P.IsZeroSide V' → P.redSnd V' = ∞̃ → D V + D V' ≤ 1))) := by
    intro V hz₁ hz₂ hDV
    rcases classBound R hR hO f h₁ h₂ hf₁ hf₂ D hD Z hDpole V hz₁ hz₂ with
      ⟨hk, hb, hb2⟩ | ⟨hk, hb, hb2⟩ | ⟨⟨hfix, hninf, hsnd⟩, hb, hb2⟩ | ⟨⟨hk, hinf, -⟩, hb, hb2⟩ |
      ⟨⟨hk, -, hsnd⟩, hb, hb2⟩
    · obtain ⟨ha0, ha1, ha⟩ := hA _ hz₁
      obtain ⟨hd, hq⟩ := ha (hDV.trans hb)
      exact Or.inl ⟨hq, Or.inl ⟨hk, hd, fun V' hne h1' hV' => (hb2 V' hne h1' hV').trans ha1⟩⟩
    · obtain ⟨hb0, hb1, hb'⟩ := hB _ hz₂
      obtain ⟨hd, hq⟩ := hb' (hDV.trans hb)
      exact Or.inr ⟨hq, Or.inl ⟨hk, hd, fun V' hne h2' hV' => (hb2 V' hne h2' hV').trans hb1⟩⟩
    · obtain ⟨ha0, ha1, ha⟩ := hA _ hz₁
      obtain ⟨hb0, hb1, hb'⟩ := hB _ hz₂
      rcases le_or_gt 1 ((P.redFst V).ord (R.residue₁ ⟨f, h₁⟩)) with hge | hlt
      · obtain ⟨hd, hq⟩ := ha hge
        have hb00 : (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩) = 0 := by
          rcases le_or_gt 1 ((P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩)) with hge' | hlt'
          · exact absurd ⟨hq, (hb' hge').2⟩ hp
          · omega
        refine Or.inl ⟨hq, Or.inr (Or.inl ⟨hfix, hninf, hd, fun V' hne hV' => ?_⟩)⟩
        have := hb2 V' hne hV'
        omega
      · have hge' : 1 ≤ (P.redSnd V).ord (R.residue₂ ⟨f, h₂⟩) := by omega
        obtain ⟨hd, hq⟩ := hb' hge'
        refine Or.inr ⟨hq, Or.inr (Or.inl ⟨hfix, hninf, by rw [← hsnd, hd], fun V' hne hV' => ?_⟩)⟩
        have := hb2 V' hne hV'
        omega
    · obtain ⟨ha0, ha1, ha⟩ := hA _ hz₁
      obtain ⟨hd, hq⟩ := ha (hDV.trans hb)
      refine Or.inl ⟨hq, Or.inr (Or.inr ⟨hk, hinf, by rw [← hinf, hd], fun V' hne hs' hV' => ?_⟩)⟩
      exact (hb2 V' hne hs' hV').trans ha1
    · obtain ⟨hb0, hb1, hb'⟩ := hB _ hz₂
      obtain ⟨hd, hq⟩ := hb' (hDV.trans hb)
      refine Or.inr ⟨hq, Or.inr (Or.inr ⟨hk, hsnd, by rw [← hsnd, hd], fun V' hne hs' hV' => ?_⟩)⟩
      exact (hb2 V' hne hs' hV').trans hb1

  have hle : D V₀ ≤ 1 := by
    obtain ⟨ha0, ha1, ha⟩ := hA _ hd₁
    obtain ⟨hb0, hb1, hb'⟩ := hB _ hd₂
    rcases classBound R hR hO f h₁ h₂ hf₁ hf₂ D hD Z hDpole V₀ hd₁ hd₂ with
      ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩ | ⟨-, hb, -⟩
    · exact hb.trans ha1
    · exact hb.trans hb1
    · refine hb.trans ?_
      rcases le_or_gt 1 ((P.redFst V₀).ord (R.residue₁ ⟨f, h₁⟩)) with hge | hlt
      · rcases le_or_gt 1 ((P.redSnd V₀).ord (R.residue₂ ⟨f, h₂⟩)) with hge' | hlt'
        · exact absurd ⟨(ha hge).2, (hb' hge').2⟩ hp
        · omega
      · omega
    · exact hb.trans ha1
    · exact hb.trans hb1
  refine ⟨le_antisymm hle hDV₀, ?_⟩

  intro V hne hDV hz₁ hz₂
  have hV := hloc V hz₁ hz₂ hDV
  have hV₀ := hloc V₀ hd₁ hd₂ hDV₀
  rcases hV with ⟨hq, hV⟩ | ⟨hq, hV⟩ <;> rcases hV₀ with ⟨hq₀, hV₀⟩ | ⟨hq₀, hV₀⟩
  ·
    rcases hV with ⟨hk, hd, hbd⟩ | ⟨hfix, hninf, hd, hbd⟩ | ⟨hk, hinf, hd, hbd⟩ <;>
      rcases hV₀ with ⟨hk₀, -, -⟩ | ⟨hfix₀, hninf₀, -, -⟩ | ⟨hk₀, hinf₀, -, -⟩
    · have := hbd V₀ (Ne.symm hne) hk₀ hd.symm; omega
    · exact hk.2 (by rw [hd]; exact hfix₀)
    · exact redFst_ne_infty_of_strict P (Or.inl hk) (by rw [hd, hinf₀])
    · exact hk₀.2 (by rw [← hd]; exact hfix)
    · have := hbd V₀ (Ne.symm hne) hd.symm; omega
    · exact hninf (by rw [hd, hinf₀])
    · exact redFst_ne_infty_of_strict P (Or.inl hk₀) hd.symm
    · exact hninf₀ hd.symm
    · have := hbd V₀ (Ne.symm hne) hk₀ hinf₀; omega
  · exact hp ⟨hq, hq₀⟩
  · exact hp ⟨hq₀, hq⟩
  ·
    rcases hV with ⟨hk, hd, hbd⟩ | ⟨hfix, hninf, hd, hbd⟩ | ⟨hk, hsnd, hd, hbd⟩ <;>
      rcases hV₀ with ⟨hk₀, -, -⟩ | ⟨hfix₀, hninf₀, hd₀, -⟩ | ⟨hk₀, hsnd₀, -, -⟩
    · have := hbd V₀ (Ne.symm hne) hk₀ hd.symm; omega
    ·
      apply hk.2
      rw [hd, ← hd₀, hfix₀]
    · exact redSnd_ne_infty_of_strict P (Or.inr hk) (by rw [hd, hsnd₀])
    · apply hk₀.2
      rw [← hd, hfix]
    ·
      have heq : P.redFst V₀ = P.redFst V := hφinj (hd₀.trans hd.symm)
      have := hbd V₀ (Ne.symm hne) heq; omega
    ·
      exact hninf (eq_infty_of_frob_eq_infty P (by rw [hd, hsnd₀]))
    · exact redSnd_ne_infty_of_strict P (Or.inr hk₀) (by rw [← hd])
    · exact hninf₀ (eq_infty_of_frob_eq_infty P (by rw [hd₀, ← hd]))
    · have := hbd V₀ (Ne.symm hne) hk₀ hsnd₀; omega

end Count

section Core

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}

set_option hygiene false in
local notation "φ" => frobOnPlacesGeomLevel (ResidueField A) 1 data hKr
set_option hygiene false in
local notation "Fq" => ↥(modularFunctionFieldBar (1 * q))
set_option hygiene false in
local notation "F1" => ↥(modularFunctionFieldC (ResidueField A) 1)
set_option hygiene false in
local notation "PlF1" => Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1)

set_option maxHeartbeats 6400000 in

private theorem mem_of_hasValue (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (Z : Finset PlF1) (G : Fq) (hG₁ : G ∈ R.R₁.integers) (hG₂ : G ∈ R.R₂.integers)
    (hGpole : ∀ W : Place (AlgebraicClosure ℚ) Fq, W.ord G < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z))
    (V₀ : Place (AlgebraicClosure ℚ) Fq) (hd₁ : P.redFst V₀ ∈ Z) (hd₂ : P.redSnd V₀ ∈ Z)
    (c : AlgebraicClosure ℚ) (hc : V₀.HasValue G c)
    (hf0 : G - algebraMap (AlgebraicClosure ℚ) Fq c ≠ 0) : c ∈ A := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) Fq :=
    ModularCurve.isCurveOver_modularFunctionFieldBar (1 * q)
  by_contra hcA
  have hc0 : c ≠ 0 := fun h => hcA (by rw [h]; exact A.zero_mem)
  have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  have ha0 := residue_inv_eq_zero_of_not_mem hcA hcinv
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) _ hf0
  have hDV₀ : 1 ≤ D V₀ := by
    have := ord_sub_pos_of_hasValue V₀ hc hf0
    rw [hD]; omega
  have hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z) := by
    intro W hW
    rw [hD] at hW
    exact hGpole W (ord_neg_of_ord_sub_const_neg W hW).2
  set H : Fq := 1 - algebraMap (AlgebraicClosure ℚ) Fq (((⟨c⁻¹, hcinv⟩ : A) : AlgebraicClosure ℚ)) * G
    with hH
  have hH₁ : H ∈ R.R₁.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem_integers₁ R _) hG₁)
  have hH₂ : H ∈ R.R₂.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem_integers₂ R _) hG₂)
  have hrH₁ : R.residue₁ ⟨H, hH₁⟩ = 1 := residue₁_one_sub_smul R G hG₁ ⟨c⁻¹, hcinv⟩ ha0 hH₁
  have hrH₂ : R.residue₂ ⟨H, hH₂⟩ = 1 := residue₂_one_sub_smul R G hG₂ ⟨c⁻¹, hcinv⟩ ha0 hH₂
  have hHf : H = algebraMap (AlgebraicClosure ℚ) Fq (-c⁻¹) * (G - algebraMap (AlgebraicClosure ℚ) Fq c) := by
    rw [hH, (algebraMap (AlgebraicClosure ℚ) Fq).map_neg, neg_mul, mul_sub, ← map_mul,
      inv_mul_cancel₀ hc0, map_one, neg_sub]
  have hDH : ∀ W, D W = W.ord H := fun W => by
    rw [hD, hHf, ord_const_mul W (neg_ne_zero.mpr (inv_ne_zero hc0))]
  rcases one_le_ord_residue_or R hR hO H hH₁ hH₂ (by rw [hrH₁]; exact one_ne_zero)
      (by rw [hrH₂]; exact one_ne_zero) D hDH Z hDpole V₀ hDV₀ hd₁ hd₂
      (show (P.redFst V₀).ord (R.residue₁ ⟨H, hH₁⟩) = 0 by rw [hrH₁, Place.ord_one]).ge
      (show (P.redSnd V₀).ord (R.residue₂ ⟨H, hH₂⟩) = 0 by rw [hrH₂, Place.ord_one]).ge with h | h
  · rw [hrH₁, Place.ord_one] at h; exact absurd h (by norm_num)
  · rw [hrH₂, Place.ord_one] at h; exact absurd h (by norm_num)

set_option maxHeartbeats 6400000 in

private theorem core_of_common_unit (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (T Z : Finset PlF1)
    (hZT : ∀ v ∈ T, v ∈ Z) (hZφ' : ∀ v, φ v ∈ T → v ∈ Z)
    (hbadZ : ∀ W : Place (AlgebraicClosure ℚ) Fq,
      (P.redFst W ∈ T ∨ P.redSnd W ∈ T) → P.redFst W ∈ Z ∧ P.redSnd W ∈ Z)
    (hZinf : P.redFst (cuspInftyBar (1 * q)) ∈ Z)
    (V₀ : Place (AlgebraicClosure ℚ) Fq) (hd₁ : P.redFst V₀ ∈ Z) (hd₂ : P.redSnd V₀ ∈ Z)
    (g₁ g₂ : F1)
    (hg₁d : (P.redFst V₀).ord (g₁ - algebraMap (ResidueField A) F1 0) = 1)
    (hg₂d : (P.redSnd V₀).ord (g₂ - algebraMap (ResidueField A) F1 1) = 1)
    (hg₁Z : ∀ z ∈ Z, z ≠ P.redFst V₀ →
      ∃ γ : ResidueField A, γ ∉ ({0, 1} : Finset (ResidueField A)) ∧ z.HasValue g₁ γ)
    (hg₂Z : ∀ z ∈ Z, z ≠ P.redSnd V₀ →
      ∃ γ : ResidueField A, γ ∉ ({0, 1} : Finset (ResidueField A)) ∧ z.HasValue g₂ γ)
    (hg₁reg : ∀ z ∈ Z, g₁ = 0 ∨ 0 ≤ z.ord g₁) (hg₂reg : ∀ z ∈ Z, g₂ = 0 ∨ 0 ≤ z.ord g₂)
    (f : Fq) (hf0 : f ≠ 0) (hf₁ : f ∈ R.R₁.integers) (hf₂ : f ∈ R.R₂.integers)
    (cbar : ResidueField A)
    (hrf₁ : R.residue₁ ⟨f, hf₁⟩ = g₁ - algebraMap (ResidueField A) F1 cbar)
    (hrf₂ : R.residue₂ ⟨f, hf₂⟩ = g₂ - algebraMap (ResidueField A) F1 cbar)
    (hfV₀ : 0 < V₀.ord f)
    (hfpole : ∀ W, W.ord f < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z)) :
    ∃ D : Divisor (AlgebraicClosure ℚ) Fq, (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
      ∀ V ∈ D.support, V ≠ V₀ → P.redFst V ∉ T ∧ P.redSnd V ∉ T := by
  classical
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) Fq :=
    ModularCurve.isCurveOver_modularFunctionFieldBar (1 * q)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  have hDV₀ : 1 ≤ D V₀ := by rw [hD]; omega
  have hDpole : ∀ W, D W < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z) := by
    intro W hW
    rw [hD] at hW
    exact hfpole W hW
  have hg₁val : (P.redFst V₀).HasValue g₁ 0 := hasValue_of_ord_sub_pos _ (by rw [hg₁d]; norm_num)
  have hg₂val : (P.redSnd V₀).HasValue g₂ 1 := hasValue_of_ord_sub_pos _ (by rw [hg₂d]; norm_num)
  have hrf₁0 : g₁ - algebraMap (ResidueField A) F1 cbar ≠ 0 := by
    intro h0
    have hconst : g₁ = algebraMap (ResidueField A) F1 cbar := sub_eq_zero.mp h0
    rw [hconst, map_zero, sub_zero, ord_algebraMap_eq_zero] at hg₁d
    exact zero_ne_one hg₁d
  have hrf₂0 : g₂ - algebraMap (ResidueField A) F1 cbar ≠ 0 := by
    intro h0
    have hconst : g₂ = algebraMap (ResidueField A) F1 cbar := sub_eq_zero.mp h0
    rw [hconst, ← map_sub, ord_algebraMap_eq_zero] at hg₂d
    exact zero_ne_one hg₂d
  have hreg₁ : 0 ≤ (P.redFst V₀).ord (g₁ - algebraMap (ResidueField A) F1 cbar) :=
    ord_sub_const_nonneg _ (hg₁reg _ hd₁) cbar
  have hreg₂ : 0 ≤ (P.redSnd V₀).ord (g₂ - algebraMap (ResidueField A) F1 cbar) :=
    ord_sub_const_nonneg _ (hg₂reg _ hd₂) cbar

  have hcb : cbar = 0 ∨ cbar = 1 := by
    rcases one_le_ord_residue_or R hR hO f hf₁ hf₂ (by rw [hrf₁]; exact hrf₁0) (by rw [hrf₂]; exact hrf₂0)
        D hD Z hDpole V₀ hDV₀ hd₁ hd₂ (by rw [hrf₁]; exact hreg₁) (by rw [hrf₂]; exact hreg₂) with h | h
    · left; rw [hrf₁] at h; exact eq_of_ord_sub_pos_of_hasValue _ hg₁val (by omega)
    · right; rw [hrf₂] at h; exact eq_of_ord_sub_pos_of_hasValue _ hg₂val (by omega)

  have hzc := eq_one_and_forall_of_orders R hR hO f hf₁ hf₂ (by rw [hrf₁]; exact hrf₁0)
    (by rw [hrf₂]; exact hrf₂0) D hD Z hZinf hDpole V₀ hDV₀ hd₁ hd₂ (cbar = 0) (cbar = 1)
    (fun h => zero_ne_one (h.1.symm.trans h.2))
    (fun z hz hzd => by
      rw [hrf₁]
      obtain ⟨γ, hγ, hv⟩ := hg₁Z z hz hzd
      refine ord_sub_eq_zero_of_hasValue_ne z hv ?_
      rintro rfl
      rcases hcb with h | h <;> simp [h] at hγ)
    (fun z hz hzd => by
      rw [hrf₂]
      obtain ⟨γ, hγ, hv⟩ := hg₂Z z hz hzd
      refine ord_sub_eq_zero_of_hasValue_ne z hv ?_
      rintro rfl
      rcases hcb with h | h <;> simp [h] at hγ)
    (fun h => by rw [hrf₁, h]; exact hg₁d)
    (fun h => by rw [hrf₁]; exact ord_sub_eq_zero_of_hasValue_ne _ hg₁val (Ne.symm h))
    (fun h => by rw [hrf₂, h]; exact hg₂d)
    (fun h => by rw [hrf₂]; exact ord_sub_eq_zero_of_hasValue_ne _ hg₂val (Ne.symm h))
  obtain ⟨hDV₀1, hothers⟩ := hzc
  refine ⟨D, hD, hDV₀1, ?_⟩
  intro V hV hVne
  have hDV : D V ≠ 0 := Finsupp.mem_support_iff.mp hV
  rcases lt_or_gt_of_ne hDV with hneg | hpos
  ·
    rcases hDpole V hneg with ⟨h1, hZ1⟩ | ⟨h2, hZ2⟩
    · refine ⟨fun hT' => hZ1 (hZT _ hT'), fun hT' => hZ1 (hZφ' _ ?_)⟩
      rw [h1.1]; exact hT'
    · refine ⟨fun hT' => hZ2 (hZφ' _ ?_), fun hT' => hZ2 (hZT _ hT')⟩
      rw [← h2.1]; exact hT'
  ·
    by_contra hbad
    have hbad' : P.redFst V ∈ T ∨ P.redSnd V ∈ T := by
      by_contra h'
      push Not at h'
      exact hbad h'
    obtain ⟨hz1, hz2⟩ := hbadZ V hbad'
    exact hothers V hVne (by omega) hz1 hz2

set_option maxHeartbeats 12800000 in
private theorem core_equiv (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q (IsLocalRing.residue A))
    (S₀ : Finset (ResidueField A)) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q (ResidueField A))
    (hNR : R.RegularityLaw S₀)
    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1)))
    (hT : ∀ t ∈ T, t ∉ ssPlaces q 1 (ResidueField A))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV₀ : P.redFst V₀ ∈ T ∨ P.redSnd V₀ ∈ T) :
    ∃ (f : ↥(modularFunctionFieldBar (1 * q)))
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      f ≠ 0 ∧ (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
        (∀ V ∈ D.support, V ≠ V₀ → P.redFst V ∉ T ∧ P.redSnd V ∉ T) ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₀ = V₀ →
            arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • f = f := by
  classical
  haveI := ValuationSubring.isAlgClosed_residueField A
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) Fq := ModularCurve.isCurveOver_modularFunctionFieldBar (1 * q)
  haveI : Infinite (ResidueField A) := inferInstance
  have hφinj := ModularCurve.frobOnPlacesGeomLevel_injective (ResidueField A) 1 data hKr

  set Z : Finset PlF1 := T ∪ T.image φ ∪ T.preimage φ hφinj.injOn ∪
    {P.redFst (cuspInftyBar (1 * q))} with hZdef
  have hZT : ∀ v ∈ T, v ∈ Z := fun v hv => by
    simp only [hZdef, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hv))
  have hZφ : ∀ v ∈ T, φ v ∈ Z := fun v hv => by
    simp only [hZdef, Finset.mem_union, Finset.mem_image]; exact Or.inl (Or.inl (Or.inr ⟨v, hv, rfl⟩))
  have hZφ' : ∀ v, φ v ∈ T → v ∈ Z := fun v hv => by
    simp only [hZdef, Finset.mem_union, Finset.mem_preimage]; exact Or.inl (Or.inr hv)
  have hZinf : P.redFst (cuspInftyBar (1 * q)) ∈ Z := by
    simp [hZdef]
  have hvinf_nss : P.redFst (cuspInftyBar (1 * q)) ∉ ssPlaces q 1 (ResidueField A) := by
    intro h
    obtain ⟨a, -, ha⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q _ _).mp h
    rw [redFst_cuspInftyBar P] at ha
    unfold charLGeomPlaceOfPoint at ha
    exact RationalFunctionField.placeOfPoint_ne_placeInfty (ResidueField A) a
      ((charLGeomPlaceEquiv (ResidueField A)).injective ha)
  have hZss : ∀ v ∈ Z, v ∉ ssPlaces q 1 (ResidueField A) := by
    intro v hv
    simp only [hZdef, Finset.mem_union, Finset.mem_image, Finset.mem_preimage, Finset.mem_singleton] at hv
    rcases hv with ((hv | ⟨w, hw, rfl⟩) | hv) | rfl
    · exact hT v hv
    · rw [frob_mem_ssPlaces_iff]; exact hT w hw
    · intro h; exact hT _ hv ((frob_mem_ssPlaces_iff (data := data) (hKr := hKr) v).mpr h)
    · exact hvinf_nss
  have hbadZ : ∀ W : Place (AlgebraicClosure ℚ) Fq, (P.redFst W ∈ T ∨ P.redSnd W ∈ T) →
      P.redFst W ∈ Z ∧ P.redSnd W ∈ Z := by
    intro W hW
    rcases P.d1 W with h | h
    · change P.redFst W = φ (P.redSnd W) at h
      rcases hW with hW | hW
      · exact ⟨hZT _ hW, hZφ' _ (by rw [← h]; exact hW)⟩
      · exact ⟨by rw [h]; exact hZφ _ hW, hZT _ hW⟩
    · change φ (P.redFst W) = P.redSnd W at h
      rcases hW with hW | hW
      · exact ⟨hZT _ hW, by rw [← h]; exact hZφ _ hW⟩
      · exact ⟨hZφ' _ (by rw [h]; exact hW), hZT _ hW⟩
  obtain ⟨hd₁, hd₂⟩ := hbadZ V₀ hV₀

  set m : ℕ := genusFF (AlgebraicClosure ℚ) Fq + S₀.card + 1 with hm
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, hinj₁, hinj₂, hB₁, hB₂, hfix₁, hfix₂⟩ :=
    ModularCurve.PlaceSpecialization.exists_families_isStrictTypeOne_isStrictTypeTwo_notMem_forall_inertia_smul_eq P Z m m
  set E₁ : Divisor (AlgebraicClosure ℚ) Fq := ∑ i, Finsupp.single (Q₁ i) (1 : ℤ) with hE₁
  set E₂ : Divisor (AlgebraicClosure ℚ) Fq := ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) with hE₂
  set Daux : Divisor (AlgebraicClosure ℚ) Fq := E₁ + E₂ with hDaux
  have hDaux0 : ∀ W, 0 ≤ Daux W := fun W => by
    rw [hDaux, Finsupp.add_apply]
    exact add_nonneg (sum_single_apply_nonneg Q₁ W) (sum_single_apply_nonneg Q₂ W)
  have hDaux_cases : ∀ W, Daux W ≠ 0 → (∃ i, Q₁ i = W) ∨ (∃ j, Q₂ j = W) := by
    intro W hW
    by_contra hc
    push Not at hc
    apply hW
    rw [hDaux, Finsupp.add_apply, sum_single_apply_eq_zero Q₁ W hc.1, sum_single_apply_eq_zero Q₂ W hc.2,
      add_zero]
  have hgood : P.IsGoodDivisor Daux := by
    intro W hW
    rcases hDaux_cases W (Finsupp.mem_support_iff.mp hW) with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl (hQ₁ i)
    · exact Or.inr (hQ₂ j)
  have hdeg : 2 * (genusFF (AlgebraicClosure ℚ) Fq : ℤ) ≤ Daux.degree + 1 := by
    rw [hDaux, map_add, hE₁, hE₂, degree_sum_single, degree_sum_single, Fintype.card_fin, hm]
    push_cast
    omega
  have hDQ₁ : ∀ i, 1 ≤ Daux (Q₁ i) := fun i => by
    rw [hDaux, Finsupp.add_apply]
    exact le_add_of_le_of_nonneg (one_le_sum_single_apply_self Q₁ i) (sum_single_apply_nonneg Q₂ _)
  have hDQ₂ : ∀ j, 1 ≤ Daux (Q₂ j) := fun j => by
    rw [hDaux, Finsupp.add_apply]
    exact le_add_of_nonneg_of_le (sum_single_apply_nonneg Q₁ _) (one_le_sum_single_apply_self Q₂ j)

  set U₁ : Finset PlF1 := Finset.univ.image (fun i => P.redFst (Q₁ i)) with hU₁
  set U₂ : Finset PlF1 := Finset.univ.image (fun j => P.redSnd (Q₂ j)) with hU₂
  have hU₁card : U₁.card = m := by
    rw [hU₁, Finset.card_image_of_injective _ hinj₁, Finset.card_univ, Fintype.card_fin]
  have hU₂card : U₂.card = m := by
    rw [hU₂, Finset.card_image_of_injective _ hinj₂, Finset.card_univ, Fintype.card_fin]
  have hmemU₁ : ∀ {v}, v ∈ U₁ → ∃ i, P.redFst (Q₁ i) = v := fun {v} hv => by
    simpa [hU₁] using hv
  have hmemU₂ : ∀ {v}, v ∈ U₂ → ∃ j, P.redSnd (Q₂ j) = v := fun {v} hv => by
    simpa [hU₂] using hv
  have hU₁mem : ∀ i, P.redFst (Q₁ i) ∈ U₁ := fun i => by
    rw [hU₁]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hU₂mem : ∀ j, P.redSnd (Q₂ j) ∈ U₂ := fun j => by
    rw [hU₂]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hU₁Z : ∀ v ∈ U₁, v ∉ Z := by
    intro v hv; obtain ⟨i, rfl⟩ := hmemU₁ hv; exact hB₁ i
  have hU₂Z : ∀ v ∈ U₂, v ∉ Z := by
    intro v hv; obtain ⟨j, rfl⟩ := hmemU₂ hv; exact hB₂ j
  have hU₁fix : ∀ v ∈ U₁, φ (φ v) ≠ v := by
    intro v hv; obtain ⟨i, rfl⟩ := hmemU₁ hv; exact (hQ₁ i).2
  have hU₂fix : ∀ v ∈ U₂, φ (φ v) ≠ v := by
    intro v hv; obtain ⟨j, rfl⟩ := hmemU₂ hv; exact (hQ₂ j).2

  have hsumU : ∀ (U : Finset PlF1) (v : PlF1),
      (∑ u ∈ U, Finsupp.single u (1 : ℤ)) v = if v ∈ U then 1 else 0 := by
    intro U v
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
  have hL₁ : riemannRochSpace (∑ u ∈ U₁, Finsupp.single u (1 : ℤ)) ≤
      riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart Daux)) := by
    refine riemannRochSpace_mono fun v => ?_
    rw [hsumU]
    unfold PlaceSpecialization.fstPart
    split_ifs with hv
    · obtain ⟨i, rfl⟩ := hmemU₁ hv
      exact le_trans (hDQ₁ i)
        (le_mapDomain_filter Daux P.IsStrictTypeOne P.redFst _ (fun W _ _ => hDaux0 W) (hQ₁ i) rfl)
    · exact mapDomain_filter_nonneg _ _ _ _ (fun W _ _ => hDaux0 W)
  have hL₂ : riemannRochSpace (∑ u ∈ U₂, Finsupp.single u (1 : ℤ)) ≤
      riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart Daux)) := by
    refine riemannRochSpace_mono fun v => ?_
    rw [hsumU]
    unfold PlaceSpecialization.sndPart
    split_ifs with hv
    · obtain ⟨j, rfl⟩ := hmemU₂ hv
      exact le_trans (hDQ₂ j)
        (le_mapDomain_filter Daux P.IsStrictTypeTwo P.redSnd _ (fun W _ _ => hDaux0 W) (hQ₂ j) rfl)
    · exact mapDomain_filter_nonneg _ _ _ _ (fun W _ _ => hDaux0 W)

  set N₁ : Finset PlF1 := S₀.image (fun a => (frobNodePair q a).1) with hN₁
  set N₂ : Finset PlF1 := S₀.image (fun a => (frobNodePair q a).2) with hN₂
  have hN₁ss : ∀ v ∈ N₁, v ∈ ssPlaces q 1 (ResidueField A) := by
    intro v hv
    rw [hN₁, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    exact frobNodePair_fst_mem_ssPlaces ((hS₀ a).mp ha)
  have hN₂ss : ∀ v ∈ N₂, v ∈ ssPlaces q 1 (ResidueField A) := by
    intro v hv
    rw [hN₂, Finset.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    exact frobNodePair_snd_mem_ssPlaces ((hS₀ a).mp ha)
  have hN₁card : N₁.card ≤ S₀.card := Finset.card_image_le
  have hN₂card : N₂.card ≤ S₀.card := Finset.card_image_le

  have he : ∀ c : ResidueField A, (ratFuncEquivCharLOneC (ResidueField A)).toRingEquiv
      (algebraMap (ResidueField A) (RatFunc (ResidueField A)) c) = algebraMap (ResidueField A) F1 c :=
    fun c => (ratFuncEquivCharLOneC (ResidueField A)).commutes c
  obtain ⟨γ₀, hγ₀⟩ := Infinite.exists_notMem_finset ({(0 : ResidueField A), 1} : Finset (ResidueField A))
  have hU₁N₁ : Disjoint U₁ N₁ := Finset.disjoint_left.mpr fun v hvU hvN =>
    hU₁fix v hvU (fixed_of_mem_ssPlaces (hN₁ss v hvN))
  have hU₂N₂ : Disjoint U₂ N₂ := Finset.disjoint_left.mpr fun v hvU hvN =>
    hU₂fix v hvU (fixed_of_mem_ssPlaces (hN₂ss v hvN))
  have hU₁Za : Disjoint U₁ (Z.erase (P.redFst V₀)) := Finset.disjoint_left.mpr fun v hvU hvZ =>
    hU₁Z v hvU (Finset.mem_of_mem_erase hvZ)
  have hU₂Za : Disjoint U₂ (Z.erase (P.redSnd V₀)) := Finset.disjoint_left.mpr fun v hvU hvZ =>
    hU₂Z v hvU (Finset.mem_of_mem_erase hvZ)
  have hN₁Za : Disjoint N₁ (Z.erase (P.redFst V₀)) := Finset.disjoint_left.mpr fun v hvN hvZ =>
    hZss v (Finset.mem_of_mem_erase hvZ) (hN₁ss v hvN)
  have hN₂Za : Disjoint N₂ (Z.erase (P.redSnd V₀)) := Finset.disjoint_left.mpr fun v hvN hvZ =>
    hZss v (Finset.mem_of_mem_erase hvZ) (hN₂ss v hvN)
  have hd₁U : P.redFst V₀ ∉ U₁ := fun h => hU₁Z _ h hd₁
  have hd₂U : P.redSnd V₀ ∉ U₂ := fun h => hU₂Z _ h hd₂
  have hd₁N : P.redFst V₀ ∉ N₁ := fun h => hZss _ hd₁ (hN₁ss _ h)
  have hd₂N : P.redSnd V₀ ∉ N₂ := fun h => hZss _ hd₂ (hN₂ss _ h)
  have hd₁Za : P.redFst V₀ ∉ Z.erase (P.redFst V₀) := Finset.notMem_erase _ _
  have hd₂Za : P.redSnd V₀ ∉ Z.erase (P.redSnd V₀) := Finset.notMem_erase _ _
  have hcard₁ : N₁.card + 1 ≤ U₁.card := by rw [hU₁card, hm]; omega
  have hcard₂ : N₂.card + 1 ≤ U₂.card := by rw [hU₂card, hm]; omega
  obtain ⟨g₁, hg₁L, hg₁d, hg₁N, hg₁Z⟩ :=
    AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
      (ratFuncEquivCharLOneC (ResidueField A)).toRingEquiv he U₁ N₁ (Z.erase (P.redFst V₀))
      (P.redFst V₀) (0 : ResidueField A) (fun _ => γ₀) {0, 1} hU₁N₁ hU₁Za hN₁Za hd₁U hd₁N hd₁Za hcard₁
  obtain ⟨g₂, hg₂L, hg₂d, hg₂N, hg₂Z⟩ :=
    AlgebraicCurve.exists_mem_riemannRochSpace_ord_sub_eq_one_hasValue_of_ringEquiv_ratFunc
      (ratFuncEquivCharLOneC (ResidueField A)).toRingEquiv he U₂ N₂ (Z.erase (P.redSnd V₀))
      (P.redSnd V₀) (1 : ResidueField A) (fun _ => γ₀) {0, 1} hU₂N₂ hU₂Za hN₂Za hd₂U hd₂N hd₂Za hcard₂
  have hg₁val : (P.redFst V₀).HasValue g₁ 0 := hasValue_of_ord_sub_pos _ (by rw [hg₁d]; norm_num)
  have hg₂val : (P.redSnd V₀).HasValue g₂ 1 := hasValue_of_ord_sub_pos _ (by rw [hg₂d]; norm_num)
  have hg₁reg : ∀ z ∈ Z, g₁ = 0 ∨ 0 ≤ z.ord g₁ := fun z hz =>
    ord_nonneg_of_mem_riemannRochSpace hg₁L z (by rw [hsumU, if_neg (fun h => hU₁Z z h hz)])
  have hg₂reg : ∀ z ∈ Z, g₂ = 0 ∨ 0 ≤ z.ord g₂ := fun z hz =>
    ord_nonneg_of_mem_riemannRochSpace hg₂L z (by rw [hsumU, if_neg (fun h => hU₂Z z h hz)])

  have hg₁F : (R.ι (toFull (ResidueField A) g₁) : F1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redFst (P.fstPart Daux)) := by
    rw [ι_toFull]; exact hL₁ hg₁L
  have hg₂F : (R.ι (toFull (ResidueField A) g₂) : F1) ∈
      riemannRochSpace (Finsupp.mapDomain P.redSnd (P.sndPart Daux)) := by
    rw [ι_toFull]; exact hL₂ hg₂L
  have hnode : ∀ a ∈ S₀, ∃ c : ResidueField A,
      (frobNodePair q a).1.HasValue (R.ι (toFull (ResidueField A) g₁) : F1) c ∧
      (frobNodePair q a).2.HasValue (R.ι (toFull (ResidueField A) g₂) : F1) c := by
    intro a ha
    refine ⟨γ₀, ?_, ?_⟩
    · rw [ι_toFull]
      exact hg₁N _ (by rw [hN₁]; exact Finset.mem_image_of_mem (fun a => (frobNodePair q a).1) ha)
    · rw [ι_toFull]
      exact hg₂N _ (by rw [hN₂]; exact Finset.mem_image_of_mem (fun a => (frobNodePair q a).2) ha)

  have hDfix : ∀ W ∈ Daux.support, ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • W = W := by
    intro W hW σ hσ
    rcases hDaux_cases W (Finsupp.mem_support_iff.mp hW) with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact hfix₁ i σ hσ
    · exact hfix₂ j σ hσ
  obtain ⟨G, hG₁, hG₂, hGL, hr₁, hr₂, hGfix⟩ :=
    R.exists_mem_riemannRochSpace_residue_eq_forall_inertia_smul_eq_of_regular_of_nonneg hR hO hval S₀ hS₀ hNR
      Daux hDaux0 hgood hdeg (toFull (ResidueField A) g₁) (toFull (ResidueField A) g₂) hg₁F hg₂F hnode V₀ hDfix
  have hres₁ : R.residue₁ ⟨G, hG₁⟩ = g₁ := by
    rw [LevelOneProlongationPair.residue₁_apply, hr₁, ι_toFull]
  have hres₂ : R.residue₂ ⟨G, hG₂⟩ = g₂ := by
    rw [LevelOneProlongationPair.residue₂_apply, hr₂, ι_toFull]
  have hg₁ne : g₁ ≠ 0 := by
    intro h; rw [h, map_zero, sub_zero, Place.ord_zero] at hg₁d; exact zero_ne_one hg₁d
  have hG0 : G ≠ 0 := by
    intro h0
    apply hg₁ne
    rw [← hres₁]
    have : (⟨G, hG₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hGpole : ∀ W, W.ord G < 0 → (∃ i, Q₁ i = W) ∨ (∃ j, Q₂ j = W) := by
    intro W hW
    apply hDaux_cases
    rcases (mem_riemannRochSpace_iff.mp hGL) W with h | h
    · exact absurd h hG0
    · omega

  have hV₀notQ : Daux V₀ = 0 := by
    by_contra h
    rcases hDaux_cases V₀ h with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hB₁ i (by rw [hi]; exact hd₁)
    · exact hB₂ j (by rw [hj]; exact hd₂)
  obtain ⟨c, hc⟩ := exists_hasValue_of_ord_nonneg V₀ (ord_nonneg_of_mem_riemannRochSpace hGL V₀ hV₀notQ)
  set f : Fq := G - algebraMap (AlgebraicClosure ℚ) Fq c with hf
  have hf0 : f ≠ 0 := by
    intro h0
    have hGc : G = algebraMap (AlgebraicClosure ℚ) Fq c := sub_eq_zero.mp h0
    have hcA : c ∈ A := (R.R₁.algebraMap_mem_iff c).mp (by rw [← hGc]; exact hG₁)
    have hconst : g₁ = algebraMap (ResidueField A) F1 (IsLocalRing.residue A ⟨c, hcA⟩) := by
      rw [← hres₁]
      have hx : (⟨G, hG₁⟩ : R.R₁.integers) =
          ⟨algebraMap (AlgebraicClosure ℚ) Fq (((⟨c, hcA⟩ : A) : AlgebraicClosure ℚ)),
            algebraMap_mem_integers₁ R ⟨c, hcA⟩⟩ := Subtype.ext hGc
      rw [hx, residue₁_algebraMap]
    rw [hconst, map_zero, sub_zero, ord_algebraMap_eq_zero] at hg₁d
    exact zero_ne_one hg₁d

  have hGpoleZ : ∀ W : Place (AlgebraicClosure ℚ) Fq, W.ord G < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z) := by
    intro W hW
    rcases hGpole W hW with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨hQ₁ i, hB₁ i⟩
    · exact Or.inr ⟨hQ₂ j, hB₂ j⟩
  have hcA : c ∈ A := mem_of_hasValue R hR hO Z G hG₁ hG₂ hGpoleZ V₀ hd₁ hd₂ c hc hf0

  have hf₁ : f ∈ R.R₁.integers := sub_mem hG₁ (algebraMap_mem_integers₁ R ⟨c, hcA⟩)
  have hf₂ : f ∈ R.R₂.integers := sub_mem hG₂ (algebraMap_mem_integers₂ R ⟨c, hcA⟩)
  set cbar : ResidueField A := IsLocalRing.residue A ⟨c, hcA⟩ with hcbar
  have hrf₁ : R.residue₁ ⟨f, hf₁⟩ = g₁ - algebraMap (ResidueField A) F1 cbar := by
    rw [← hres₁]; exact residue₁_sub_algebraMap R G hG₁ ⟨c, hcA⟩ hf₁
  have hrf₂ : R.residue₂ ⟨f, hf₂⟩ = g₂ - algebraMap (ResidueField A) F1 cbar := by
    rw [← hres₂]; exact residue₂_sub_algebraMap R G hG₂ ⟨c, hcA⟩ hf₂
  have hfV₀ : 0 < V₀.ord f := ord_sub_pos_of_hasValue V₀ hc hf0
  have hfpole : ∀ W, W.ord f < 0 →
      (P.IsStrictTypeOne W ∧ P.redFst W ∉ Z) ∨ (P.IsStrictTypeTwo W ∧ P.redSnd W ∉ Z) :=
    fun W hW => hGpoleZ W (ord_neg_of_ord_sub_const_neg W hW).2
  obtain ⟨D, hD, hDV₀1, hgood'⟩ := core_of_common_unit R hR hO T Z hZT hZφ' hbadZ hZinf V₀ hd₁ hd₂
    g₁ g₂ hg₁d hg₂d (fun z hz hne => hg₁Z z (Finset.mem_erase.mpr ⟨hne, hz⟩))
    (fun z hz hne => hg₂Z z (Finset.mem_erase.mpr ⟨hne, hz⟩)) hg₁reg hg₂reg f hf0 hf₁ hf₂ cbar hrf₁ hrf₂ hfV₀ hfpole

  have hffix : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₀ = V₀ →
        arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • f = f := by
    intro σ hσ hσV₀
    have hG := hGfix σ hσ hσV₀
    have hcσ : SemilinearAut.baseAut (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ) c = c := by
      have h := hasValue_smul_semilinear (arithmeticGalois (modularFunctionFieldFull (1 * q)) σ) hc
      rw [hσV₀, hG] at h
      exact (hc.unique h).symm
    rw [hf, smul_sub, hG, SemilinearAut.smul_algebraMap, hcσ]
  exact ⟨f, D, hf0, hD, hDV₀1, hgood', hffix⟩

end Core

end MOV1Core
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField.MOV1Core"

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [CharP (ResidueField A) q] [DecidableEq (ResidueField A)]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ}
    (R : P.LevelOneProlongationPair) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (hval : LevelOneProlongationPair.NodeValueLaw q (IsLocalRing.residue A))
    (S₀ : Finset (ResidueField A)) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q (ResidueField A))
    (hNR : R.RegularityLaw S₀)
    (T : Finset (Place (ResidueField A) ↥(modularFunctionFieldC (ResidueField A) 1)))
    (hT : ∀ t ∈ T, t ∉ ssPlaces q 1 (ResidueField A))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hV₀ : P.redFst V₀ ∈ T ∨ P.redSnd V₀ ∈ T) :
    ∃ (f : ↥(modularFunctionFieldBar (1 * q)))
      (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))),
      f ≠ 0 ∧ (∀ V, D V = V.ord f) ∧ D V₀ = 1 ∧
        (∀ V ∈ D.support, V ≠ V₀ → P.redFst V ∉ T ∧ P.redSnd V ∉ T) ∧
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V₀ = V₀ →
            arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • f = f :=
  MOV1Core.core_equiv R hR hO hval S₀ hS₀ hNR T hT V₀ hV₀

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_ord_eq_one_forall_redFst_redSnd_notMem_forall_inertia_smul_eq_residueField (solution)
