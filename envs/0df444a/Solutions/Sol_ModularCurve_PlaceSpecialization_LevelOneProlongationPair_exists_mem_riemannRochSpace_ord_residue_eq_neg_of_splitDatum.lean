-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a90cf539-3a6e-59ed-a3eb-2fea163c960f

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_GluedPic0
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_exists_forall_coeff_smul_mem_of_forall_ord_neg
import Theorems.Thm_ModularCurve_exists_linearIndependent_residuePair_of_finiteDimensional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
import Theorems.Thm_AlgebraicCurve_finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
import Theorems.Thm_ModularCurve_LevelOneFibre_genusFF_lt_card_of_ssJSet
import Theorems.Thm_ModularCurve_degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_linearIndependent_map_prod_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
import Theorems.Thm_AlgebraicCurve_exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
import Theorems.Thm_P2M_Dup_AlgebraicCurve_RationalFunctionField_eq_placeOfPoint_or_eq_placeInfty
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two"
p2m_attr_erase "simp" "compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ HahnSeries.coeff_hahnTwist ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

namespace FltWs29
namespace C2v3

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

section AlphaGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem Alpha.ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ≠ 0) (h : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f :=
  ((v.adicValuation_le_one_iff).mp (v.adicValuation_le_one_of_mem h)).resolve_left hf

theorem Alpha.mem_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le h
  rw [hu, hn, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem π.2 n)

theorem Alpha.ord_neg_of_ord_sub_neg (v : Place K F) {f g : F} (hg : g ∈ v.toValuationSubring)
    (h : v.ord (f - g) < 0) : v.ord f < 0 := by
  rw [← Place.not_adicValuation_le_one_iff] at h ⊢
  intro hf
  apply h
  calc v.adicValuation (f - g) ≤ max (v.adicValuation f) (v.adicValuation g) := Valuation.map_sub _ _ _
    _ ≤ 1 := max_le hf (v.adicValuation_le_one_of_mem hg)

theorem Alpha.ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · exact (Place.hasValue_algebraMap v c).ord_eq_zero hc

theorem Alpha.ord_smul_const (v : Place K F) {c : K} (hc : c ≠ 0) (f : F) : v.ord (c • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [Algebra.smul_def, v.ord_mul ((map_ne_zero _).mpr hc) hf, Alpha.ord_algebraMap, zero_add]

theorem Alpha.ord_pow (v : Place K F) (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have h := v.ord_zpow f n
  rwa [zpow_natCast] at h

theorem Alpha.ord_sub_pos_of_hasValue (v : Place K F) {g : F} {c : K} (h : v.HasValue g c)
    (hne : g ≠ algebraMap K F c) : 0 < v.ord (g - algebraMap K F c) := by
  have hmem : g - algebraMap K F c ∈ v.toValuationSubring := sub_mem h.mem (v.algebraMap_mem' c)
  have hne0 : g - algebraMap K F c ≠ 0 := sub_ne_zero.mpr hne
  have h0 : 0 ≤ v.ord (g - algebraMap K F c) := Alpha.ord_nonneg_of_mem v hne0 hmem
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hne0 heq.symm
    have e : (⟨g - algebraMap K F c, hm⟩ : v.toValuationSubring)
        = ⟨g, h.mem⟩ - algebraMap K v.toValuationSubring c := Subtype.ext rfl
    have hres : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F c, hm⟩ = 0 := by
      rw [e, map_sub, h.residue_eq, Place.residue_algebraMap, sub_self]
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu) hres

theorem Alpha.exists_hasValue_of_deg_eq_one (v : Place K F) (hdeg : v.deg = 1) {g : F}
    (hg : g ∈ v.toValuationSubring) : ∃ a : K, v.HasValue g a := by
  have h1 : (1 : v.ResidueField) ≠ 0 := one_ne_zero
  have hsurj : Function.Surjective (algebraMap K v.ResidueField) := by
    intro x
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) h1).mp hdeg x
    exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩
  obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective hsurj hg
  exact ⟨a, ha⟩

theorem Alpha.inv_mem_of_isUnit {S : ValuationSubring F} {x : F} (hx : x ∈ S)
    (hu : IsUnit (⟨x, hx⟩ : S)) : x⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := hu
  have hcoe : ((u : S) : F) = x := by rw [hu]
  have h1 : x * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← hcoe, ← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  have hinv : (((u⁻¹ : Sˣ) : S) : F) = x⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  exact hinv ▸ SetLike.coe_mem _

theorem Alpha.coe_unit_inv {S : ValuationSubring F} (u : Sˣ) :
    (((u⁻¹ : Sˣ) : S) : F) = ((u : S) : F)⁻¹ := by
  have h1 : ((u : S) : F) * (((u⁻¹ : Sˣ) : S) : F) = 1 := by
    rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  exact (inv_eq_of_mul_eq_one_right h1).symm

theorem Alpha.exists_coeffMap_subtype_eq {L : Type*} [Field L] (A : ValuationSubring L)
    (x : LaurentSeries L) (hx : ∀ n : ℤ, x.coeff n ∈ A) :
    ∃ y : LaurentSeries A, coeffMap A.subtype y = x := by
  refine ⟨⟨fun n => ⟨x.coeff n, hx n⟩, ?_⟩, ?_⟩
  · convert x.isPWO_support' using 1
    ext n
    simp only [Function.mem_support, ne_eq]
    rw [← ZeroMemClass.coe_eq_zero]
  · ext n
    rfl

theorem Alpha.coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R) :
    coeffMap f (HahnSeries.C r) = HahnSeries.C (f r) :=
  HahnSeries.map_C r f

theorem Alpha.coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

end AlphaGeneric

section AlphaLevel

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem Alpha.neZero : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩

theorem Alpha.isFrickeAutFull : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have key : ∀ (n : ℕ) [NeZero n], n = q → IsFrickeAutFull n (frickeInvolutionFull n) := by
    rintro n _ rfl
    exact isFrickeAutFull_frickeInvolutionFull_prime _
  exact key (1 * q) (one_mul q)

theorem Alpha.w_mul_self : frickeInvolutionBar (1 * q) * frickeInvolutionBar (1 * q) = 1 := by
  haveI : NeZero (1 * q) := Alpha.neZero
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  exact frickeInvolutionBar_frickeInvolutionBar (1 * q) y

theorem Alpha.w_w (y : modularFunctionFieldBar (1 * q)) :
    frickeInvolutionBar (1 * q) (frickeInvolutionBar (1 * q) y) = y := by
  haveI : NeZero (1 * q) := Alpha.neZero
  exact frickeInvolutionBar_frickeInvolutionBar (1 * q) y

theorem Alpha.w_smul_w_smul (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    frickeInvolutionBar (1 * q) • (frickeInvolutionBar (1 * q) • W) = W := by
  rw [smul_smul, Alpha.w_mul_self, one_smul]

theorem Alpha.w_jqFun : frickeInvolutionBar (1 * q) (jqFun (q := q)) = jFun (q := q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) Alpha.isFrickeAutFull (1 * q) 1 (mul_one _)
  apply Subtype.ext
  have h' : ((frickeInvolutionBar (1 * q) (jqFun (q := q)) : modularFunctionFieldBar (1 * q)) :
      LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) :=
    congrArg Subtype.val h
  rw [qExpand_one_apply] at h'
  exact h'

theorem Alpha.w_jFun : frickeInvolutionBar (1 * q) (jFun (q := q)) = jqFun (q := q) := by
  have h := congrArg (frickeInvolutionBar (1 * q)) (Alpha.w_jqFun (q := q))
  rw [Alpha.w_w] at h
  exact h.symm

theorem Alpha.w_smul_cuspInftyBar :
    frickeInvolutionBar (1 * q) • cuspInftyBar (1 * q) = cuspZeroBar (1 * q) :=
  (cuspZeroBar_def (1 * q)).symm

theorem Alpha.w_smul_cuspZeroBar :
    frickeInvolutionBar (1 * q) • cuspZeroBar (1 * q) = cuspInftyBar (1 * q) := by
  rw [cuspZeroBar_def, Alpha.w_smul_w_smul]

theorem Alpha.ord_w (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (g : modularFunctionFieldBar (1 * q)) :
    W.ord (frickeInvolutionBar (1 * q) g) = (frickeInvolutionBar (1 * q) • W).ord g := by
  conv_lhs => rw [← Alpha.w_smul_w_smul W]
  rw [Place.ord_smul]

theorem Alpha.ord_cuspInftyBar_jFun : (cuspInftyBar (1 * q)).ord (jFun (q := q)) = -1 := by
  haveI : NeZero (1 * q) := Alpha.neZero
  exact ord_cuspInftyBar_coeffEmb_jq (1 * q)

theorem Alpha.ord_cuspZeroBar_jFun : (cuspZeroBar (1 * q)).ord (jFun (q := q)) = -((1 * q : ℕ) : ℤ) := by
  haveI : NeZero (1 * q) := Alpha.neZero
  exact ord_cuspZeroBar_coeffEmb_jq (1 * q) Alpha.isFrickeAutFull

theorem Alpha.one_le_level : (1 : ℤ) ≤ ((1 * q : ℕ) : ℤ) := by
  have h : 1 ≤ 1 * q := by rw [one_mul]; exact (Fact.out : q.Prime).one_lt.le
  exact_mod_cast h

theorem Alpha.jFun_ne_zero : (jFun (q := q)) ≠ 0 := by
  intro h
  have h1 := Alpha.ord_cuspInftyBar_jFun (q := q)
  rw [h, Place.ord_zero] at h1
  norm_num at h1

theorem Alpha.jqFun_ne_zero : (jqFun (q := q)) ≠ 0 := by
  rw [← Alpha.w_jFun]
  exact (map_ne_zero _).mpr Alpha.jFun_ne_zero

theorem Alpha.jFun_ne_algebraMap (c : AlgebraicClosure ℚ) :
    (jFun (q := q)) ≠ algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c := by
  intro h
  have h1 := Alpha.ord_cuspInftyBar_jFun (q := q)
  rw [h, Alpha.ord_algebraMap] at h1
  norm_num at h1

theorem Alpha.ord_jFun_neg_iff (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    W.ord (jFun (q := q)) < 0 ↔ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by
  refine ⟨eq_cuspInftyBar_or_eq_cuspZeroBar_of_ord_jFun_neg W, ?_⟩
  rintro (rfl | rfl)
  · rw [Alpha.ord_cuspInftyBar_jFun]; norm_num
  · rw [Alpha.ord_cuspZeroBar_jFun, neg_lt_zero]
    exact lt_of_lt_of_le zero_lt_one Alpha.one_le_level

theorem Alpha.ord_jqFun_neg_iff (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    W.ord (jqFun (q := q)) < 0 ↔ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by
  rw [← Alpha.w_jFun, Alpha.ord_w, Alpha.ord_jFun_neg_iff]
  constructor
  · rintro (h | h)
    · right; rw [← Alpha.w_smul_w_smul W, h, Alpha.w_smul_cuspInftyBar]
    · left; rw [← Alpha.w_smul_w_smul W, h, Alpha.w_smul_cuspZeroBar]
  · rintro (rfl | rfl)
    · right; exact Alpha.w_smul_cuspInftyBar
    · left; exact Alpha.w_smul_cuspZeroBar

theorem Alpha.not_cusp_of_smul {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))}
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q)) :
    frickeInvolutionBar (1 * q) • W ≠ cuspInftyBar (1 * q) ∧
      frickeInvolutionBar (1 * q) • W ≠ cuspZeroBar (1 * q) := by
  constructor
  · intro h; apply h0; rw [← Alpha.w_smul_w_smul W, h, Alpha.w_smul_cuspInftyBar]
  · intro h; apply hinf; rw [← Alpha.w_smul_w_smul W, h, Alpha.w_smul_cuspZeroBar]

theorem Alpha.coe_jFun :
    ((jFun (q := q) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = jqModC (AlgebraicClosure ℚ) := by
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) jq = _
  rw [← jqModC_rat]
  exact Alpha.coeffMap_jqModC _

theorem Alpha.coe_jqFun :
    ((jqFun (q := q) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = qExpand (AlgebraicClosure ℚ) (1 * q) (jqModC (AlgebraicClosure ℚ)) := by
  haveI : NeZero (1 * q) := Alpha.neZero
  show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (qExpand ℚ (1 * q) jq) = _
  rw [coeffMap_qExpand, ← jqModC_rat, Alpha.coeffMap_jqModC]

noncomputable def Alpha.uJ (b : A) : modularFunctionFieldBar (1 * q) :=
  algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (b : AlgebraicClosure ℚ) * jFun (q := q) - 1

noncomputable def Alpha.uJq (b : A) : modularFunctionFieldBar (1 * q) :=
  algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (b : AlgebraicClosure ℚ) * jqFun (q := q) - 1

theorem Alpha.w_uJ (b : A) : frickeInvolutionBar (1 * q) (Alpha.uJ (q := q) b) = Alpha.uJq b := by
  unfold Alpha.uJ Alpha.uJq
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, Alpha.w_jFun]

theorem Alpha.w_uJq (b : A) : frickeInvolutionBar (1 * q) (Alpha.uJq (q := q) b) = Alpha.uJ b := by
  unfold Alpha.uJ Alpha.uJq
  rw [map_sub, map_mul, map_one, AlgEquiv.commutes, Alpha.w_jqFun]

theorem Alpha.coe_uJ (b : A) :
    ((Alpha.uJ (q := q) b : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (HahnSeries.C b * jqModC A - 1) := by
  haveI : NeZero (1 * q) := Alpha.neZero
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, Alpha.coeffMap_jqModC]
  unfold Alpha.uJ
  have hc : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (b : AlgebraicClosure ℚ) :
      modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (b : AlgebraicClosure ℚ) := rfl
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, Alpha.coe_jFun, hc,
    algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  try rfl

theorem Alpha.coe_uJq (b : A) :
    ((Alpha.uJq (q := q) b : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffMap A.subtype (HahnSeries.C b * qExpand A (1 * q) (jqModC A) - 1) := by
  haveI : NeZero (1 * q) := Alpha.neZero
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, coeffMap_qExpand, Alpha.coeffMap_jqModC]
  unfold Alpha.uJq
  have hc : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (b : AlgebraicClosure ℚ) :
      modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (b : AlgebraicClosure ℚ) := rfl
  rw [AddSubgroupClass.coe_sub, MulMemClass.coe_mul, OneMemClass.coe_one, Alpha.coe_jqFun, hc,
    algebraMap_laurentSeries_eq_single, HahnSeries.C_apply]
  try rfl

theorem Alpha.coeffMap_residue_yJ (b : A) (hb : b ∈ maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C b * jqModC A - 1) = -1 := by
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb,
    map_zero, zero_mul, zero_sub]

theorem Alpha.coeffMap_residue_yJq (b : A) (hb : b ∈ maximalIdeal A) :
    coeffMap (IsLocalRing.residue A) (HahnSeries.C b * qExpand A (1 * q) (jqModC A) - 1) = -1 := by
  haveI : NeZero (1 * q) := Alpha.neZero
  rw [map_sub, map_mul, map_one, Alpha.coeffMap_C, (IsLocalRing.residue_eq_zero_iff b).mpr hb,
    map_zero, zero_mul, zero_sub]

theorem Alpha.eq_cusp_of_ord_uJ_neg (b : A) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h : W.ord (Alpha.uJ (q := q) b) < 0) : W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by
  have h1 : W.ord (algebraMap _ _ (b : AlgebraicClosure ℚ) * jFun (q := q)) < 0 :=
    Alpha.ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : (b : AlgebraicClosure ℚ) ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) Alpha.jFun_ne_zero, Alpha.ord_algebraMap, zero_add] at h1
  exact (Alpha.ord_jFun_neg_iff W).mp h1

theorem Alpha.eq_cusp_of_ord_uJq_neg (b : A) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (h : W.ord (Alpha.uJq (q := q) b) < 0) : W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by
  have h1 : W.ord (algebraMap _ _ (b : AlgebraicClosure ℚ) * jqFun (q := q)) < 0 :=
    Alpha.ord_neg_of_ord_sub_neg W (one_mem _) h
  have hb : (b : AlgebraicClosure ℚ) ≠ 0 := by
    intro hb; rw [hb, map_zero, zero_mul, Place.ord_zero] at h1; exact lt_irrefl _ h1
  rw [W.ord_mul ((map_ne_zero _).mpr hb) Alpha.jqFun_ne_zero, Alpha.ord_algebraMap, zero_add] at h1
  exact (Alpha.ord_jqFun_neg_iff W).mp h1

theorem Alpha.uJ_ne_zero (b : A) : Alpha.uJ (q := q) b ≠ 0 := by
  intro h
  have h' : algebraMap _ _ (b : AlgebraicClosure ℚ) * jFun (q := q) = 1 := sub_eq_zero.mp h
  rcases eq_or_ne (b : AlgebraicClosure ℚ) 0 with hb | hb
  · rw [hb, map_zero, zero_mul] at h'; exact zero_ne_one h'
  · have h1 := congrArg (cuspInftyBar (1 * q)).ord h'
    rw [(cuspInftyBar (1 * q)).ord_mul ((map_ne_zero _).mpr hb) Alpha.jFun_ne_zero, Alpha.ord_algebraMap,
      Alpha.ord_cuspInftyBar_jFun, Place.ord_one] at h1
    norm_num at h1

theorem Alpha.uJq_ne_zero (b : A) : Alpha.uJq (q := q) b ≠ 0 := by
  rw [← Alpha.w_uJ]
  exact (map_ne_zero _).mpr (Alpha.uJ_ne_zero b)

theorem Alpha.uJ_mem_place (b : A) {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))}
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q)) :
    Alpha.uJ (q := q) b ∈ W.toValuationSubring :=
  Alpha.mem_of_ord_nonneg W (Alpha.uJ_ne_zero b) (not_lt.mp fun h => by
    rcases Alpha.eq_cusp_of_ord_uJ_neg b W h with rfl | rfl <;> contradiction)

theorem Alpha.uJq_mem_place (b : A) {W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))}
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q)) :
    Alpha.uJq (q := q) b ∈ W.toValuationSubring :=
  Alpha.mem_of_ord_nonneg W (Alpha.uJq_ne_zero b) (not_lt.mp fun h => by
    rcases Alpha.eq_cusp_of_ord_uJq_neg b W h with rfl | rfl <;> contradiction)

theorem Alpha.exists_uJ_of_tate (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q))
    (hcusp : ∀ a : A, W.ord (jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (Alpha.uJ (q := q) b) := by
  haveI : NeZero (1 * q) := Alpha.neZero
  have hj0 : 0 ≤ W.ord (jFun (q := q)) := not_lt.mp fun h => by
    rcases (Alpha.ord_jFun_neg_iff W).mp h with rfl | rfl <;> contradiction
  have hmem : (jFun (q := q)) ∈ W.toValuationSubring := Alpha.mem_of_ord_nonneg W Alpha.jFun_ne_zero hj0
  obtain ⟨c, hc⟩ := Alpha.exists_hasValue_of_deg_eq_one W (deg_eq_one_modularFunctionFieldBar (1 * q) W) hmem
  have hpos : 0 < W.ord (jFun (q := q) - algebraMap _ _ c) :=
    Alpha.ord_sub_pos_of_hasValue W hc (Alpha.jFun_ne_algebraMap c)
  have hcA : c ∉ A := fun hcA => absurd (hcusp ⟨c, hcA⟩) (not_le.mpr hpos)
  have hc0 : c ≠ 0 := fun h => hcA (h ▸ A.zero_mem)
  have hbA : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
  refine ⟨⟨c⁻¹, hbA⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hcA
    have h2 := Alpha.inv_mem_of_isUnit hbA hu
    rwa [inv_inv] at h2
  · have e : Alpha.uJ (q := q) ⟨c⁻¹, hbA⟩ = algebraMap _ _ (c⁻¹ : AlgebraicClosure ℚ) * (jFun (q := q) - algebraMap _ _ c) := by
      unfold Alpha.uJ
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ hc0, map_one]
    rw [e, W.ord_mul ((map_ne_zero _).mpr (inv_ne_zero hc0)) (sub_ne_zero.mpr (Alpha.jFun_ne_algebraMap c)),
      Alpha.ord_algebraMap, zero_add]
    exact hpos

theorem Alpha.exists_uJq_of_tate (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q))
    (hcusp : ∀ a : A, W.ord (jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    ∃ b : A, b ∈ maximalIdeal A ∧ 0 < W.ord (Alpha.uJq (q := q) b) := by
  have h' : ∀ a : A, (frickeInvolutionBar (1 * q) • W).ord (jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have e : frickeInvolutionBar (1 * q) (jFun (q := q) - algebraMap _ _ (a : AlgebraicClosure ℚ))
        = jqFun (q := q) - algebraMap _ _ (a : AlgebraicClosure ℚ) := by
      rw [map_sub, Alpha.w_jFun, AlgEquiv.commutes]
    rw [← Alpha.ord_w, e]
    exact hcusp a
  obtain ⟨hwinf, hw0⟩ := Alpha.not_cusp_of_smul hinf h0
  obtain ⟨b, hb, hpos⟩ := Alpha.exists_uJ_of_tate _ hwinf hw0 h'
  refine ⟨b, hb, ?_⟩
  rw [← Alpha.w_uJ, Alpha.ord_w]
  exact hpos

end AlphaLevel

end FltWs29.C2v3

namespace FltWs29
namespace C2v3

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

section AlphaU1

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem Alpha.exists_coeffMap_eq_smul_of_poles (f : modularFunctionFieldBar (1 * q)) (hf : f ≠ 0)
    (hpole : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      (∃ a : A, 0 < W.ord (jFun (q := q)
        - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
      ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q)) :
    ∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
      coeffMap A.subtype y = c • (f : LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : NeZero (1 * q) := Alpha.neZero
  obtain ⟨M, hM1, hM2⟩ : ∃ M : ℕ, -(cuspInftyBar (1 * q)).ord f ≤ M ∧ -(cuspZeroBar (1 * q)).ord f ≤ M :=
    ⟨(-(cuspInftyBar (1 * q)).ord f).toNat + (-(cuspZeroBar (1 * q)).ord f).toNat, by omega, by omega⟩
  have hJ0 : (jFun (q := q))⁻¹ ^ M ≠ 0 := pow_ne_zero _ (inv_ne_zero Alpha.jFun_ne_zero)
  have hg0 : f * (jFun (q := q))⁻¹ ^ M ≠ 0 := mul_ne_zero hf hJ0
  have hordg : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      W.ord (f * (jFun (q := q))⁻¹ ^ M) = W.ord f - M * W.ord (jFun (q := q)) := fun W => by
    rw [W.ord_mul hf hJ0, Alpha.ord_pow, W.ord_inv]; ring
  obtain ⟨c, hc0, hc⟩ := exists_forall_coeff_smul_mem_of_forall_ord_neg A (1 * q) _ hg0 (by
    intro W hW
    rw [hordg] at hW
    rcases lt_trichotomy (W.ord (jFun (q := q))) 0 with hj | hj | hj
    · exfalso
      rcases (Alpha.ord_jFun_neg_iff W).mp hj with rfl | rfl
      · rw [Alpha.ord_cuspInftyBar_jFun] at hW
        omega
      · rw [Alpha.ord_cuspZeroBar_jFun] at hW
        have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg _
        have h3 : (M : ℤ) ≤ M * ((1 * q : ℕ) : ℤ) := le_mul_of_one_le_right hM0 Alpha.one_le_level
        have h4 : (cuspZeroBar (1 * q)).ord f + M * ((1 * q : ℕ) : ℤ) < 0 := by linarith
        linarith
    · rw [hj, mul_zero, sub_zero] at hW
      rcases hpole W hW with h | rfl | rfl
      · exact h
      · exfalso; rw [Alpha.ord_cuspInftyBar_jFun] at hj; norm_num at hj
      · exfalso
        rw [Alpha.ord_cuspZeroBar_jFun] at hj
        have h1 := Alpha.one_le_level (q := q)
        omega
    · refine ⟨0, ?_⟩
      rw [ZeroMemClass.coe_zero, map_zero, sub_zero]
      exact hj)
  obtain ⟨yg, hyg⟩ := Alpha.exists_coeffMap_subtype_eq A _ hc
  have hJne : jqModC (AlgebraicClosure ℚ) ≠ 0 := by
    rw [← Alpha.coe_jFun (q := q)]
    exact fun h => Alpha.jFun_ne_zero (q := q) ((ZeroMemClass.coe_eq_zero).mp h)
  have hJ : ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ M * (jqModC (AlgebraicClosure ℚ)) ^ M = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hJne, one_pow]
  refine ⟨c, yg * (jqModC A) ^ M, hc0, ?_⟩
  rw [map_mul, map_pow, hyg, Alpha.coeffMap_jqModC, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
    IntermediateField.coe_inv, Alpha.coe_jFun, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    mul_assoc, mul_assoc, hJ, mul_one]

theorem Alpha.poles_mul (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (U : modularFunctionFieldBar (1 * q)) (hU0 : U ≠ 0)
    (hUint : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      W ≠ cuspInftyBar (1 * q) → W ≠ cuspZeroBar (1 * q) → U ∈ W.toValuationSubring)
    (T : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → Prop)
    (hUT : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
      W ≠ cuspInftyBar (1 * q) → W ≠ cuspZeroBar (1 * q) → 0 < E W → T W → E W ≤ W.ord U)
    (f : modularFunctionFieldBar (1 * q)) (hf : f ∈ riemannRochSpace E) (hf0 : f ≠ 0)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : W.ord (U * f) < 0) :
    ¬ T W ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q) := by
  by_cases hinf : W = cuspInftyBar (1 * q)
  · exact Or.inr (Or.inl hinf)
  by_cases h0 : W = cuspZeroBar (1 * q)
  · exact Or.inr (Or.inr h0)
  left
  intro hT
  have hU : 0 ≤ W.ord U := Alpha.ord_nonneg_of_mem W hU0 (hUint W hinf h0)
  rw [W.ord_mul hU0 hf0] at hW
  rcases (mem_riemannRochSpace_iff.mp hf) W with h | h
  · exact hf0 h
  · have hEW : 0 < E W := by omega
    have h2 := hUT W hinf h0 hEW hT
    omega

end AlphaU1

section AlphaPair

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem Alpha.uJ_mem₁ (R : P.LevelOneProlongationPair) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJ (q := q) b ∈ R.R₁.integers, R.R₁.residue ⟨Alpha.uJ b, h⟩ = -1 := by
  haveI : NeZero (1 * q) := Alpha.neZero
  have hy : coeffMap A.subtype (HahnSeries.C b * jqModC A - 1) ∈ modularFunctionFieldBar (1 * q) := by
    rw [← Alpha.coe_uJ (q := q)]; exact (Alpha.uJ (q := q) b).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨coeffMap A.subtype (HahnSeries.C b * jqModC A - 1), hy⟩ : modularFunctionFieldBar (1 * q))
      = Alpha.uJ b := Subtype.ext (Alpha.coe_uJ b).symm
  have h' : Alpha.uJ (q := q) b ∈ R.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨Alpha.uJ b, h'⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hres, Alpha.coeffMap_residue_yJ b hb, NegMemClass.coe_neg, OneMemClass.coe_one]

theorem Alpha.uJq_mem₁ (R : P.LevelOneProlongationPair) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJq (q := q) b ∈ R.R₁.integers, R.R₁.residue ⟨Alpha.uJq b, h⟩ = -1 := by
  haveI : NeZero (1 * q) := Alpha.neZero
  have hy : coeffMap A.subtype (HahnSeries.C b * qExpand A (1 * q) (jqModC A) - 1)
      ∈ modularFunctionFieldBar (1 * q) := by
    rw [← Alpha.coe_uJq (q := q)]; exact (Alpha.uJq (q := q) b).2
  obtain ⟨h, hres⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨coeffMap A.subtype (HahnSeries.C b * qExpand A (1 * q) (jqModC A) - 1), hy⟩ :
      modularFunctionFieldBar (1 * q)) = Alpha.uJq b := Subtype.ext (Alpha.coe_uJq b).symm
  have h' : Alpha.uJq (q := q) b ∈ R.R₁.integers := by rw [← e]; exact h
  refine ⟨h', ?_⟩
  have e2 : (⟨Alpha.uJq b, h'⟩ : R.R₁.integers) = ⟨_, h⟩ := Subtype.ext e.symm
  rw [e2]
  apply Subtype.ext
  rw [hres, Alpha.coeffMap_residue_yJq b hb, NegMemClass.coe_neg, OneMemClass.coe_one]

theorem Alpha.uJ_mem₂ (R : P.LevelOneProlongationPair) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJ (q := q) b ∈ R.R₂.integers, R.R₂.residue ⟨Alpha.uJ b, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := Alpha.uJq_mem₁ R b hb
  have h1' : frickeInvolutionBar (1 * q) (Alpha.uJ (q := q) b) ∈ R.R₁.integers := by
    rw [Alpha.w_uJ]; exact h1
  have h2 : Alpha.uJ (q := q) b ∈ R.R₂.integers := (R.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [R.residue₂_eq]
  have e : (⟨frickeInvolutionBar (1 * q) (Alpha.uJ b), (R.mem_integers₂_iff _).mp h2⟩ : R.R₁.integers)
      = ⟨Alpha.uJq b, h1⟩ := Subtype.ext (Alpha.w_uJ b)
  rw [e, hres]

theorem Alpha.uJq_mem₂ (R : P.LevelOneProlongationPair) (b : A) (hb : b ∈ maximalIdeal A) :
    ∃ h : Alpha.uJq (q := q) b ∈ R.R₂.integers, R.R₂.residue ⟨Alpha.uJq b, h⟩ = -1 := by
  obtain ⟨h1, hres⟩ := Alpha.uJ_mem₁ R b hb
  have h1' : frickeInvolutionBar (1 * q) (Alpha.uJq (q := q) b) ∈ R.R₁.integers := by
    rw [Alpha.w_uJq]; exact h1
  have h2 : Alpha.uJq (q := q) b ∈ R.R₂.integers := (R.mem_integers₂_iff _).mpr h1'
  refine ⟨h2, ?_⟩
  rw [R.residue₂_eq]
  have e : (⟨frickeInvolutionBar (1 * q) (Alpha.uJq b), (R.mem_integers₂_iff _).mp h2⟩ : R.R₁.integers)
      = ⟨Alpha.uJ b, h1⟩ := Subtype.ext (Alpha.w_uJq b)
  rw [e, hres]

noncomputable def Alpha.bigU (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A) :
    modularFunctionFieldBar (1 * q) :=
  (∏ W ∈ E.support, Alpha.uJ (q := q) (bJ W) ^ (E W).toNat) *
    ∏ W ∈ E.support, Alpha.uJq (q := q) (bJq W) ^ (E W).toNat

theorem Alpha.bigU_ne_zero (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A) :
    Alpha.bigU (q := q) E bJ bJq ≠ 0 :=
  mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (Alpha.uJ_ne_zero _))
    (Finset.prod_ne_zero_iff.mpr fun W _ => pow_ne_zero _ (Alpha.uJq_ne_zero _))

theorem Alpha.bigU_mem_place (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q)) :
    Alpha.bigU (q := q) E bJ bJq ∈ W.toValuationSubring :=
  mul_mem (prod_mem fun W' _ => pow_mem (Alpha.uJ_mem_place _ hinf h0) _)
    (prod_mem fun W' _ => pow_mem (Alpha.uJq_mem_place _ hinf h0) _)

theorem Alpha.le_ord_bigU_of_pos (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q)) (hEW : 0 < E W)
    (hpos : 0 < W.ord (Alpha.uJ (q := q) (bJ W))) :
    E W ≤ W.ord (Alpha.bigU (q := q) E bJ bJq) := by
  classical
  have hWS : W ∈ E.support := Finsupp.mem_support_iff.mpr hEW.ne'
  have hsplit := Finset.mul_prod_erase E.support (fun W' => Alpha.uJ (q := q) (bJ W') ^ (E W').toNat) hWS
  unfold Alpha.bigU
  rw [← hsplit]
  have hne1 : Alpha.uJ (q := q) (bJ W) ^ (E W).toNat ≠ 0 := pow_ne_zero _ (Alpha.uJ_ne_zero _)
  have hne2 : ∏ x ∈ E.support.erase W, Alpha.uJ (q := q) (bJ x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJ_ne_zero _)
  have hne3 : ∏ x ∈ E.support, Alpha.uJq (q := q) (bJq x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJq_ne_zero _)
  rw [W.ord_mul (mul_ne_zero hne1 hne2) hne3, W.ord_mul hne1 hne2, Alpha.ord_pow]
  have h2 : 0 ≤ W.ord (∏ x ∈ E.support.erase W, Alpha.uJ (q := q) (bJ x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne2 (prod_mem fun W' _ => pow_mem (Alpha.uJ_mem_place _ hinf h0) _)
  have h3 : 0 ≤ W.ord (∏ x ∈ E.support, Alpha.uJq (q := q) (bJq x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne3 (prod_mem fun W' _ => pow_mem (Alpha.uJq_mem_place _ hinf h0) _)
  have h4 : ((E W).toNat : ℤ) = E W := Int.toNat_of_nonneg hEW.le
  have h5 : ((E W).toNat : ℤ) * 1 ≤ ((E W).toNat : ℤ) * W.ord (Alpha.uJ (q := q) (bJ W)) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  linarith

theorem Alpha.le_ord_bigU_of_pos' (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hinf : W ≠ cuspInftyBar (1 * q)) (h0 : W ≠ cuspZeroBar (1 * q)) (hEW : 0 < E W)
    (hpos : 0 < W.ord (Alpha.uJq (q := q) (bJq W))) :
    E W ≤ W.ord (Alpha.bigU (q := q) E bJ bJq) := by
  classical
  have hWS : W ∈ E.support := Finsupp.mem_support_iff.mpr hEW.ne'
  have hsplit := Finset.mul_prod_erase E.support (fun W' => Alpha.uJq (q := q) (bJq W') ^ (E W').toNat) hWS
  unfold Alpha.bigU
  rw [← hsplit]
  have hne1 : Alpha.uJq (q := q) (bJq W) ^ (E W).toNat ≠ 0 := pow_ne_zero _ (Alpha.uJq_ne_zero _)
  have hne2 : ∏ x ∈ E.support.erase W, Alpha.uJq (q := q) (bJq x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJq_ne_zero _)
  have hne3 : ∏ x ∈ E.support, Alpha.uJ (q := q) (bJ x) ^ (E x).toNat ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W' _ => pow_ne_zero _ (Alpha.uJ_ne_zero _)
  rw [W.ord_mul hne3 (mul_ne_zero hne1 hne2), W.ord_mul hne1 hne2, Alpha.ord_pow]
  have h2 : 0 ≤ W.ord (∏ x ∈ E.support.erase W, Alpha.uJq (q := q) (bJq x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne2 (prod_mem fun W' _ => pow_mem (Alpha.uJq_mem_place _ hinf h0) _)
  have h3 : 0 ≤ W.ord (∏ x ∈ E.support, Alpha.uJ (q := q) (bJ x) ^ (E x).toNat) :=
    Alpha.ord_nonneg_of_mem W hne3 (prod_mem fun W' _ => pow_mem (Alpha.uJ_mem_place _ hinf h0) _)
  have h4 : ((E W).toNat : ℤ) = E W := Int.toNat_of_nonneg hEW.le
  have h5 : ((E W).toNat : ℤ) * 1 ≤ ((E W).toNat : ℤ) * W.ord (Alpha.uJq (q := q) (bJq W)) :=
    mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
  linarith

theorem Alpha.bigU_isUnit₁ (R : P.LevelOneProlongationPair)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A)
    (hbJ : ∀ W, bJ W ∈ maximalIdeal A) (hbJq : ∀ W, bJq W ∈ maximalIdeal A) :
    ∃ h : Alpha.bigU (q := q) E bJ bJq ∈ R.R₁.integers, IsUnit (⟨Alpha.bigU E bJ bJq, h⟩ : R.R₁.integers) := by
  classical
  have m1 : ∀ W, Alpha.uJ (q := q) (bJ W) ∈ R.R₁.integers := fun W => (Alpha.uJ_mem₁ R (bJ W) (hbJ W)).1
  have m2 : ∀ W, Alpha.uJq (q := q) (bJq W) ∈ R.R₁.integers := fun W => (Alpha.uJq_mem₁ R (bJq W) (hbJq W)).1
  have r1 : ∀ W, R.R₁.residue ⟨Alpha.uJ (q := q) (bJ W), m1 W⟩ = -1 := fun W => (Alpha.uJ_mem₁ R (bJ W) (hbJ W)).2
  have r2 : ∀ W, R.R₁.residue ⟨Alpha.uJq (q := q) (bJq W), m2 W⟩ = -1 := fun W => (Alpha.uJq_mem₁ R (bJq W) (hbJq W)).2
  set y1 : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → R.R₁.integers :=
    fun W => ⟨Alpha.uJ (q := q) (bJ W), m1 W⟩ with hy1
  set y2 : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → R.R₁.integers :=
    fun W => ⟨Alpha.uJq (q := q) (bJq W), m2 W⟩ with hy2
  set x : R.R₁.integers := (∏ W ∈ E.support, y1 W ^ (E W).toNat) * ∏ W ∈ E.support, y2 W ^ (E W).toNat with hx
  have e1 : ((∏ W ∈ E.support, y1 W ^ (E W).toNat : R.R₁.integers) : modularFunctionFieldBar (1 * q))
      = ∏ W ∈ E.support, ((y1 W ^ (E W).toNat : R.R₁.integers) : modularFunctionFieldBar (1 * q)) :=
    by first | exact SubmonoidClass.coe_finset_prod _ _ | exact SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ W ∈ E.support, y2 W ^ (E W).toNat : R.R₁.integers) : modularFunctionFieldBar (1 * q))
      = ∏ W ∈ E.support, ((y2 W ^ (E W).toNat : R.R₁.integers) : modularFunctionFieldBar (1 * q)) :=
    by first | exact SubmonoidClass.coe_finset_prod _ _ | exact SubmonoidClass.coe_finsetProd _ _
  have hxU : (x : modularFunctionFieldBar (1 * q)) = Alpha.bigU E bJ bJq := by
    rw [hx, MulMemClass.coe_mul, e1, e2]
    unfold Alpha.bigU
    congr 1 <;> first | rfl | exact Finset.prod_congr rfl fun W _ => (by rw [SubmonoidClass.coe_pow])
  have hmem : Alpha.bigU (q := q) E bJ bJq ∈ R.R₁.integers := by rw [← hxU]; exact x.2
  refine ⟨hmem, ?_⟩
  have ex : (⟨Alpha.bigU E bJ bJq, hmem⟩ : R.R₁.integers) = x := Subtype.ext hxU.symm
  rw [ex]
  apply R.R₁.isUnit_of_residue_ne_zero
  rw [hx, map_mul, map_prod, map_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => ?_) (Finset.prod_ne_zero_iff.mpr fun W _ => ?_)
  · rw [map_pow, r1]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [map_pow, r2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

theorem Alpha.bigU_isUnit₂ (R : P.LevelOneProlongationPair)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (bJ bJq : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → A)
    (hbJ : ∀ W, bJ W ∈ maximalIdeal A) (hbJq : ∀ W, bJq W ∈ maximalIdeal A) :
    ∃ h : Alpha.bigU (q := q) E bJ bJq ∈ R.R₂.integers, IsUnit (⟨Alpha.bigU E bJ bJq, h⟩ : R.R₂.integers) := by
  classical
  have m1 : ∀ W, Alpha.uJ (q := q) (bJ W) ∈ R.R₂.integers := fun W => (Alpha.uJ_mem₂ R (bJ W) (hbJ W)).1
  have m2 : ∀ W, Alpha.uJq (q := q) (bJq W) ∈ R.R₂.integers := fun W => (Alpha.uJq_mem₂ R (bJq W) (hbJq W)).1
  have r1 : ∀ W, R.R₂.residue ⟨Alpha.uJ (q := q) (bJ W), m1 W⟩ = -1 := fun W => (Alpha.uJ_mem₂ R (bJ W) (hbJ W)).2
  have r2 : ∀ W, R.R₂.residue ⟨Alpha.uJq (q := q) (bJq W), m2 W⟩ = -1 := fun W => (Alpha.uJq_mem₂ R (bJq W) (hbJq W)).2
  set y1 : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → R.R₂.integers :=
    fun W => ⟨Alpha.uJ (q := q) (bJ W), m1 W⟩ with hy1
  set y2 : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) → R.R₂.integers :=
    fun W => ⟨Alpha.uJq (q := q) (bJq W), m2 W⟩ with hy2
  set x : R.R₂.integers := (∏ W ∈ E.support, y1 W ^ (E W).toNat) * ∏ W ∈ E.support, y2 W ^ (E W).toNat with hx
  have e1 : ((∏ W ∈ E.support, y1 W ^ (E W).toNat : R.R₂.integers) : modularFunctionFieldBar (1 * q))
      = ∏ W ∈ E.support, ((y1 W ^ (E W).toNat : R.R₂.integers) : modularFunctionFieldBar (1 * q)) :=
    by first | exact SubmonoidClass.coe_finset_prod _ _ | exact SubmonoidClass.coe_finsetProd _ _
  have e2 : ((∏ W ∈ E.support, y2 W ^ (E W).toNat : R.R₂.integers) : modularFunctionFieldBar (1 * q))
      = ∏ W ∈ E.support, ((y2 W ^ (E W).toNat : R.R₂.integers) : modularFunctionFieldBar (1 * q)) :=
    by first | exact SubmonoidClass.coe_finset_prod _ _ | exact SubmonoidClass.coe_finsetProd _ _
  have hxU : (x : modularFunctionFieldBar (1 * q)) = Alpha.bigU E bJ bJq := by
    rw [hx, MulMemClass.coe_mul, e1, e2]
    unfold Alpha.bigU
    congr 1 <;> first | rfl | exact Finset.prod_congr rfl fun W _ => (by rw [SubmonoidClass.coe_pow])
  have hmem : Alpha.bigU (q := q) E bJ bJq ∈ R.R₂.integers := by rw [← hxU]; exact x.2
  refine ⟨hmem, ?_⟩
  have ex : (⟨Alpha.bigU E bJ bJq, hmem⟩ : R.R₂.integers) = x := Subtype.ext hxU.symm
  rw [ex]
  apply R.R₂.isUnit_of_residue_ne_zero
  rw [hx, map_mul, map_prod, map_prod]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun W _ => ?_) (Finset.prod_ne_zero_iff.mpr fun W _ => ?_)
  · rw [map_pow, r1]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · rw [map_pow, r2]; exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)

theorem Alpha.exists_bigU (R : P.LevelOneProlongationPair)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    ∃ U : modularFunctionFieldBar (1 * q),
      (∃ h₁ : U ∈ R.R₁.integers, IsUnit (⟨U, h₁⟩ : R.R₁.integers)) ∧
      (∃ h₂ : U ∈ R.R₂.integers, IsUnit (⟨U, h₂⟩ : R.R₂.integers)) ∧
      (∀ f ∈ riemannRochSpace E, f ≠ 0 →
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord (U * f) < 0 →
          (∃ a : A, 0 < W.ord (jFun (q := q)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
          ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q)) ∧
      (∀ f ∈ riemannRochSpace E, f ≠ 0 →
        ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord (U * f) < 0 →
          (∃ a : A, 0 < W.ord (jqFun (q := q)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
          ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q)) := by
  classical

  have hJ : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), ∃ b : A, b ∈ maximalIdeal A ∧
      (W ≠ cuspInftyBar (1 * q) → W ≠ cuspZeroBar (1 * q) →
        (∀ a : A, W.ord (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) ≤ 0) → 0 < W.ord (Alpha.uJ (q := q) b)) := by
    intro W
    by_cases h : W ≠ cuspInftyBar (1 * q) ∧ W ≠ cuspZeroBar (1 * q) ∧
        ∀ a : A, W.ord (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := Alpha.exists_uJ_of_tate W h.1 h.2.1 h.2.2
      exact ⟨b, hb, fun _ _ _ => hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  have hJq : ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), ∃ b : A, b ∈ maximalIdeal A ∧
      (W ≠ cuspInftyBar (1 * q) → W ≠ cuspZeroBar (1 * q) →
        (∀ a : A, W.ord (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) ≤ 0) → 0 < W.ord (Alpha.uJq (q := q) b)) := by
    intro W
    by_cases h : W ≠ cuspInftyBar (1 * q) ∧ W ≠ cuspZeroBar (1 * q) ∧
        ∀ a : A, W.ord (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) ≤ 0
    · obtain ⟨b, hb, hpos⟩ := Alpha.exists_uJq_of_tate W h.1 h.2.1 h.2.2
      exact ⟨b, hb, fun _ _ _ => hpos⟩
    · exact ⟨0, Ideal.zero_mem _, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose bJ hbJm hbJpos using hJ
  choose bJq hbJqm hbJqpos using hJq
  refine ⟨Alpha.bigU E bJ bJq, Alpha.bigU_isUnit₁ R E bJ bJq hbJm hbJqm,
    Alpha.bigU_isUnit₂ R E bJ bJq hbJm hbJqm, ?_, ?_⟩
  · intro f hf hf0 W hW
    rcases Alpha.poles_mul E _ (Alpha.bigU_ne_zero E bJ bJq) (Alpha.bigU_mem_place E bJ bJq)
      (fun W => ∀ a : A, W.ord (jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) ≤ 0)
      (fun W hinf h0 hEW hT => Alpha.le_ord_bigU_of_pos E bJ bJq W hinf h0 hEW (hbJpos W hinf h0 hT))
      f hf hf0 W hW with h | h | h
    · left; simpa only [not_forall, not_le] using h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro f hf hf0 W hW
    rcases Alpha.poles_mul E _ (Alpha.bigU_ne_zero E bJ bJq) (Alpha.bigU_mem_place E bJ bJq)
      (fun W => ∀ a : A, W.ord (jqFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
          (a : AlgebraicClosure ℚ)) ≤ 0)
      (fun W hinf h0 hEW hT => Alpha.le_ord_bigU_of_pos' E bJ bJq W hinf h0 hEW (hbJqpos W hinf h0 hT))
      f hf hf0 W hW with h | h | h
    · left; simpa only [not_forall, not_le] using h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end AlphaPair

end FltWs29.C2v3

namespace FltWs29
namespace C2v3

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.PlaceSpecialization"

section AlphaMain

theorem Alpha.linearIndependent_mul_units {k₀ L : Type*} [Field k₀] [Field L] [Algebra k₀ L]
    {ι : Type*} {r : ι → L × L} (hr : LinearIndependent k₀ r) {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent k₀ (fun i => (a * (r i).1, b * (r i).2)) := by
  let φ : L × L →ₗ[k₀] L × L := (LinearMap.mulLeft k₀ a).prodMap (LinearMap.mulLeft k₀ b)
  have hφ : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h' : (a * x, b * y) = (a * x', b * y') := h
    simp only [Prod.mk.injEq] at h'
    exact Prod.ext (mul_left_cancel₀ ha h'.1) (mul_left_cancel₀ hb h'.2)
  exact hr.map' φ hφ

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

theorem Alpha.hint (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (U : modularFunctionFieldBar (1 * q)) (hU0 : U ≠ 0)
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord (jFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
        ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q))
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord (jqFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
        ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q))
    (V : Submodule (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hV : V = (riemannRochSpace E).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U))
    [FiniteDimensional (AlgebraicClosure ℚ) V] :
    ∃ b : Fin (Module.finrank (AlgebraicClosure ℚ) V) → modularFunctionFieldBar (1 * q),
      (∀ i, b i ∈ V) ∧ LinearIndependent (AlgebraicClosure ℚ) b ∧
      ∀ i, (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((b i : modularFunctionFieldBar (1 * q)) :
                LaurentSeries (AlgebraicClosure ℚ))) ∧
           (∃ (c : AlgebraicClosure ℚ) (y : LaurentSeries A), c ≠ 0 ∧
              coeffMap A.subtype y = c • ((frickeInvolutionBar (1 * q) (b i) :
                modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ))) := by
  classical
  haveI : NeZero (1 * q) := Alpha.neZero
  have B : Module.Basis (Fin (Module.finrank (AlgebraicClosure ℚ) V)) (AlgebraicClosure ℚ) V :=
    Module.finBasis (AlgebraicClosure ℚ) V
  have hbli : LinearIndependent (AlgebraicClosure ℚ) (V.subtype ∘ B) :=
    B.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hmem : ∀ i, ∃ f, f ∈ riemannRochSpace E ∧ f ≠ 0 ∧ (V.subtype ∘ B) i = U * f := fun i => by
    have hi : ((V.subtype ∘ B) i) ∈ (riemannRochSpace E).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U) :=
      hV.le (B i).2
    rw [Submodule.mem_map] at hi
    obtain ⟨f, hf, hfe⟩ := hi
    rw [LinearMap.mulLeft_apply] at hfe
    refine ⟨f, hf, ?_, hfe.symm⟩
    rintro rfl
    apply B.ne_zero i
    apply Subtype.ext
    rw [mul_zero] at hfe
    exact hfe.symm
  refine ⟨V.subtype ∘ B, fun i => (B i).2, hbli, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hf0, hfe⟩ := hmem i
    have hne : (V.subtype ∘ B) i ≠ 0 := by rw [hfe]; exact mul_ne_zero hU0 hf0
    exact Alpha.exists_coeffMap_eq_smul_of_poles _ hne (fun W hW => hpJ f hf hf0 W (by rw [← hfe]; exact hW))
  · obtain ⟨f, hf, hf0, hfe⟩ := hmem i
    have hne : (V.subtype ∘ B) i ≠ 0 := by rw [hfe]; exact mul_ne_zero hU0 hf0
    have hwne : frickeInvolutionBar (1 * q) ((V.subtype ∘ B) i) ≠ 0 := (map_ne_zero _).mpr hne
    refine Alpha.exists_coeffMap_eq_smul_of_poles _ hwne (fun W hW => ?_)
    rw [Alpha.ord_w, hfe] at hW
    rcases hpJq f hf hf0 _ hW with ⟨a, ha⟩ | h | h
    · left
      refine ⟨a, ?_⟩
      have e : frickeInvolutionBar (1 * q) (jFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))
          = jqFun (q := q) - algebraMap _ _ (a : AlgebraicClosure ℚ) := by
        rw [map_sub, Alpha.w_jFun, AlgEquiv.commutes]
      rw [← e, Alpha.ord_w, Alpha.w_smul_w_smul] at ha
      exact ha
    · right; right
      rw [← Alpha.w_smul_w_smul W, h, Alpha.w_smul_cuspInftyBar]
    · right; left
      rw [← Alpha.w_smul_w_smul W, h, Alpha.w_smul_cuspZeroBar]

set_option maxHeartbeats 6400000 in

theorem Alpha.main_of_unit (R : P.LevelOneProlongationPair)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)]
    (U : modularFunctionFieldBar (1 * q))
    (hU₁ : U ∈ R.R₁.integers) (hU₁u : IsUnit (⟨U, hU₁⟩ : R.R₁.integers))
    (hU₂ : U ∈ R.R₂.integers) (hU₂u : IsUnit (⟨U, hU₂⟩ : R.R₂.integers))
    (hpJ : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord (jFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
        ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q))
    (hpJq : ∀ f ∈ riemannRochSpace E, f ≠ 0 →
      ∀ W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)), W.ord (U * f) < 0 →
        (∃ a : A, 0 < W.ord (jqFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)))
        ∨ W = cuspInftyBar (1 * q) ∨ W = cuspZeroBar (1 * q)) :
    ∃ (Gf : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → modularFunctionFieldBar (1 * q))
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace E) ∧
      LinearIndependent (ResidueField A)
        (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) := by
  classical
  haveI : NeZero (1 * q) := Alpha.neZero
  have hU0 : U ≠ 0 := fun h => hU₁u.ne_zero (Subtype.ext h)
  have hinj : Function.Injective (LinearMap.mulLeft (AlgebraicClosure ℚ) U) := by
    intro x y h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hU0 h
  have hn : Module.finrank (AlgebraicClosure ℚ)
        ↥((riemannRochSpace E).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U))
      = Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj (riemannRochSpace E))).symm
  obtain ⟨b, hbV, hbli, hbint⟩ := Alpha.hint E U hU0 hpJ hpJq
    ((riemannRochSpace E).map (LinearMap.mulLeft (AlgebraicClosure ℚ) U)) rfl
  obtain ⟨G, hG₁, hG₂, hGV, hGli⟩ :=
    exists_linearIndependent_residuePair_of_finiteDimensional R.R₁ R.R₂ R.residue₁_coeffMap
      R.mem_integers₂_iff R.residue₂_eq _ ⟨b, hbV, hbli, hbint⟩

  obtain ⟨u₁, hu₁⟩ := hU₁u
  obtain ⟨u₂, hu₂⟩ := hU₂u
  have hcoe₁ : ((u₁ : R.R₁.integers) : modularFunctionFieldBar (1 * q)) = U := by rw [hu₁]
  have hcoe₂ : ((u₂ : R.R₂.integers) : modularFunctionFieldBar (1 * q)) = U := by rw [hu₂]
  have hinv₁ : (((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) : modularFunctionFieldBar (1 * q)) = U⁻¹ := by
    rw [Alpha.coe_unit_inv, hcoe₁]
  have hinv₂ : (((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) : modularFunctionFieldBar (1 * q)) = U⁻¹ := by
    rw [Alpha.coe_unit_inv, hcoe₂]

  set e := finCongr hn with he
  set Gf : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → modularFunctionFieldBar (1 * q) :=
    fun j => U⁻¹ * G (e.symm j) with hGf
  have hUinv₁ : U⁻¹ ∈ R.R₁.integers := by rw [← hinv₁]; exact SetLike.coe_mem _
  have hUinv₂ : U⁻¹ ∈ R.R₂.integers := by rw [← hinv₂]; exact SetLike.coe_mem _
  have hGf₁ : ∀ j, Gf j ∈ R.R₁.integers := fun j => by
    show U⁻¹ * G (e.symm j) ∈ R.R₁.integers
    exact mul_mem hUinv₁ (hG₁ _)
  have hGf₂ : ∀ j, Gf j ∈ R.R₂.integers := fun j => by
    show U⁻¹ * G (e.symm j) ∈ R.R₂.integers
    exact mul_mem hUinv₂ (hG₂ _)
  have hGfV : ∀ j, Gf j ∈ riemannRochSpace E := fun j => by
    obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.mp (hGV (e.symm j))
    rw [LinearMap.mulLeft_apply] at hfe
    have : Gf j = f := by
      rw [hGf]
      show U⁻¹ * G (e.symm j) = f
      rw [← hfe, ← mul_assoc, inv_mul_cancel₀ hU0, one_mul f]
    rw [this]; exact hf

  have ha₁ : R.R₁.residue ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) ≠ 0 :=
    R.R₁.residue_ne_zero_of_isUnit (Units.isUnit _)
  have ha₂ : R.R₂.residue ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) ≠ 0 :=
    R.R₂.residue_ne_zero_of_isUnit (Units.isUnit _)
  have hres₁ : ∀ j, R.R₁.residue ⟨Gf j, hGf₁ j⟩
      = R.R₁.residue ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) * R.R₁.residue ⟨G (e.symm j), hG₁ _⟩ := by
    intro j
    have ex : (⟨Gf j, hGf₁ j⟩ : R.R₁.integers)
        = ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers) * ⟨G (e.symm j), hG₁ _⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hinv₁]
    rw [ex, map_mul]
  have hres₂ : ∀ j, R.R₂.residue ⟨Gf j, hGf₂ j⟩
      = R.R₂.residue ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) * R.R₂.residue ⟨G (e.symm j), hG₂ _⟩ := by
    intro j
    have ex : (⟨Gf j, hGf₂ j⟩ : R.R₂.integers)
        = ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers) * ⟨G (e.symm j), hG₂ _⟩ := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, hinv₂]
    rw [ex, map_mul]
  refine ⟨Gf, hGf₁, hGf₂, hGfV, ?_⟩
  have hfun : (fun j => (R.R₁.residue ⟨Gf j, hGf₁ j⟩, R.R₂.residue ⟨Gf j, hGf₂ j⟩))
      = fun j => (R.R₁.residue ((u₁⁻¹ : (R.R₁.integers)ˣ) : R.R₁.integers)
          * ((fun i => (R.R₁.residue ⟨G i, hG₁ i⟩, R.R₂.residue ⟨G i, hG₂ i⟩)) (e.symm j)).1,
        R.R₂.residue ((u₂⁻¹ : (R.R₂.integers)ˣ) : R.R₂.integers)
          * ((fun i => (R.R₁.residue ⟨G i, hG₁ i⟩, R.R₂.residue ⟨G i, hG₂ i⟩)) (e.symm j)).2) :=
    funext fun j => Prod.ext (hres₁ j) (hres₂ j)
  rw [hfun]
  exact Alpha.linearIndependent_mul_units (hGli.comp e.symm e.symm.injective) ha₁ ha₂

theorem alpha_exists_linearIndependent_residuePair
    (R : P.LevelOneProlongationPair)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)] :
    ∃ (Gf : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → modularFunctionFieldBar (1 * q))
      (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers),
      (∀ j, Gf j ∈ riemannRochSpace E) ∧
      LinearIndependent (ResidueField A)
        (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) := by
  obtain ⟨U, ⟨hU₁, hU₁u⟩, ⟨hU₂, hU₂u⟩, hpJ, hpJq⟩ := Alpha.exists_bigU R E
  exact Alpha.main_of_unit R E U hU₁ hU₁u hU₂ hU₂u hpJ hpJq

end AlphaMain

end FltWs29.C2v3

namespace FltWs29
namespace C2v3

section Generic

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem hvZero (v : Place K F) : v.HasValue (0 : F) 0 := by
  simpa using Place.hasValue_algebraMap v (0 : K)

theorem hvAdd {v : Place K F} {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hvConstMul {v : Place K F} {g : F} {a : K} (c : K) (h : v.HasValue g a) :
    v.HasValue (c • g) (c * a) := by
  rw [Algebra.smul_def]
  exact (Place.hasValue_algebraMap v c).mul h

def twistedPairs (E₁ E₂ : Divisor K F) {ι : Type*} (v₁ v₂ : ι → Place K F) (t₁ t₂ : ι → F)
    (lam : ι → K) : Submodule K (F × F) where
  carrier := {p | p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
    ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c}
  zero_mem' := ⟨Submodule.zero_mem _, Submodule.zero_mem _, fun i =>
    ⟨0, by simpa using hvZero (v₁ i), by simpa using hvZero (v₂ i)⟩⟩
  add_mem' := by
    rintro p p' ⟨hp1, hp2, hp⟩ ⟨hq1, hq2, hq⟩
    refine ⟨Submodule.add_mem _ hp1 hq1, Submodule.add_mem _ hp2 hq2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    obtain ⟨d, hd1, hd2⟩ := hq i
    refine ⟨c + d, ?_, ?_⟩
    · simpa [mul_add] using hvAdd hc1 hd1
    · simpa [mul_add] using hvAdd hc2 hd2
  smul_mem' := by
    rintro a p ⟨hp1, hp2, hp⟩
    refine ⟨Submodule.smul_mem _ a hp1, Submodule.smul_mem _ a hp2, fun i => ?_⟩
    obtain ⟨c, hc1, hc2⟩ := hp i
    refine ⟨a * c, ?_, ?_⟩
    · have := hvConstMul a hc1
      rw [Prod.smul_fst, mul_smul_comm]
      convert this using 1
      ring
    · have := hvConstMul a hc2
      rw [Prod.smul_snd, mul_smul_comm]
      exact this

theorem mem_twistedPairs_iff {E₁ E₂ : Divisor K F} {ι : Type*} {v₁ v₂ : ι → Place K F}
    {t₁ t₂ : ι → F} {lam : ι → K} {p : F × F} :
    p ∈ twistedPairs E₁ E₂ v₁ v₂ t₁ t₂ lam ↔ p.1 ∈ riemannRochSpace E₁ ∧ p.2 ∈ riemannRochSpace E₂ ∧
      ∀ i, ∃ c : K, (v₁ i).HasValue (t₁ i * p.1) (lam i * c) ∧ (v₂ i).HasValue (t₂ i * p.2) c :=
  Iff.rfl

end Generic

section Bridge

variable (k : Type*) [Field k]

theorem charLGeomPlaceOfPoint_eq_congrEquiv (a : k) :
    charLGeomPlaceOfPoint k a = Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv
      (fun c => (ratFuncEquivCharLOneC k).commutes c) (RationalFunctionField.placeOfPoint k a) := rfl

theorem frobNodePair_fst_eq_congrEquiv (q : ℕ) (a : k) :
    (frobNodePair q a).1 = Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv
      (fun c => (ratFuncEquivCharLOneC k).commutes c) (RationalFunctionField.placeOfPoint k a) := rfl

theorem frobNodePair_snd_eq_congrEquiv (q : ℕ) (a : k) :
    (frobNodePair q a).2 = Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv
      (fun c => (ratFuncEquivCharLOneC k).commutes c) (RationalFunctionField.placeOfPoint k (a ^ q)) := rfl

theorem ratFuncEquivCharLOneC_X :
    (ratFuncEquivCharLOneC k).toRingEquiv RatFunc.X = (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) := by
  apply Subtype.ext
  show ((ratFuncEquivCharLOneC k RatFunc.X : modularFunctionFieldC k 1) : LaurentSeries k) = jqModC k
  rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)

theorem ratFuncEquivCharLOneC_C (a : k) :
    (ratFuncEquivCharLOneC k).toRingEquiv (RatFunc.C a) = algebraMap k (modularFunctionFieldC k 1) a := by
  rw [← RatFunc.algebraMap_eq_C]
  exact (ratFuncEquivCharLOneC k).commutes a

theorem ratFuncEquivCharLOneC_X_sub_C (a : k) :
    (ratFuncEquivCharLOneC k).toRingEquiv (RatFunc.X - RatFunc.C a)
      = (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a := by
  rw [map_sub, ratFuncEquivCharLOneC_X, ratFuncEquivCharLOneC_C]

theorem hasValue_twist_iff (a : k) (n : ℤ) (g : modularFunctionFieldC k 1) (c : k) :
    (charLGeomPlaceOfPoint k a).HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a) ^ n * g) c ↔
    (Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        (RationalFunctionField.placeOfPoint k a)).HasValue
      ((ratFuncEquivCharLOneC k).toRingEquiv (RatFunc.X - RatFunc.C a) ^ n * g) c := by
  rw [ratFuncEquivCharLOneC_X_sub_C]
  rfl

end Bridge

section BetaMain

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

noncomputable def splitTarget (q : ℕ) (S₀ : Finset k) (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) :
    Submodule k (↥(modularFunctionFieldC k 1) × ↥(modularFunctionFieldC k 1)) :=
  twistedPairs D₁ D₂ (fun s : ↥S₀ => (frobNodePair q (s : k)).1) (fun s : ↥S₀ => (frobNodePair q (s : k)).2)
    (fun s : ↥S₀ => ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
        - algebraMap k (modularFunctionFieldC k 1) (s : k)) ^ (D₁ (frobNodePair q (s : k)).1))
    (fun s : ↥S₀ => ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
        - algebraMap k (modularFunctionFieldC k 1) ((s : k) ^ q)) ^ (D₂ (frobNodePair q (s : k)).2))
    (fun s : ↥S₀ => lam s)

omit [Fact q.Prime] [CharP k q] [IsAlgClosed k] [DecidableEq k] in
theorem mem_splitTarget_iff {S₀ : Finset k} {D₁ D₂ : Divisor k (modularFunctionFieldC k 1)} {lam : k → k}
    {p : ↥(modularFunctionFieldC k 1) × ↥(modularFunctionFieldC k 1)} :
    p ∈ splitTarget q S₀ D₁ D₂ lam ↔ p.1 ∈ riemannRochSpace D₁ ∧ p.2 ∈ riemannRochSpace D₂ ∧
    ∀ s : ↥S₀, ∃ c : k,
      (frobNodePair q (s : k)).1.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
            - algebraMap k (modularFunctionFieldC k 1) (s : k)) ^ (D₁ (frobNodePair q (s : k)).1) * p.1)
        (lam s * c) ∧
      (frobNodePair q (s : k)).2.HasValue
        (((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1)
            - algebraMap k (modularFunctionFieldC k 1) ((s : k) ^ q)) ^ (D₂ (frobNodePair q (s : k)).2) * p.2)
        c :=
  Iff.rfl

omit [Fact q.Prime] [CharP k q] [IsAlgClosed k] [DecidableEq k] in

theorem mem_splitTarget_iff' {S₀ : Finset k} {D₁ D₂ : Divisor k (modularFunctionFieldC k 1)} {lam : k → k}
    (p : ↥(modularFunctionFieldC k 1) × ↥(modularFunctionFieldC k 1)) :
    p ∈ splitTarget q S₀ D₁ D₂ lam ↔ p.1 ∈ riemannRochSpace D₁ ∧ p.2 ∈ riemannRochSpace D₂ ∧
    ∀ s : ↥S₀, ∃ c : k,
      (Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
          (RationalFunctionField.placeOfPoint k ((fun s : ↥S₀ => (s : k)) s))).HasValue
        ((ratFuncEquivCharLOneC k).toRingEquiv (RatFunc.X - RatFunc.C ((fun s : ↥S₀ => (s : k)) s)) ^
            (D₁ (Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
              (RationalFunctionField.placeOfPoint k ((fun s : ↥S₀ => (s : k)) s)))) * p.1)
        ((fun s : ↥S₀ => lam s) s * c) ∧
      (Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
          (RationalFunctionField.placeOfPoint k ((fun s : ↥S₀ => (s : k) ^ q) s))).HasValue
        ((ratFuncEquivCharLOneC k).toRingEquiv (RatFunc.X - RatFunc.C ((fun s : ↥S₀ => (s : k) ^ q) s)) ^
            (D₂ (Place.congrEquiv (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
              (RationalFunctionField.placeOfPoint k ((fun s : ↥S₀ => (s : k) ^ q) s)))) * p.2)
        c := by
  simp only [mem_splitTarget_iff, ratFuncEquivCharLOneC_X_sub_C]
  exact Iff.rfl

set_option maxHeartbeats 6400000 in
theorem residuePair_mem_splitTarget
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (f : modularFunctionFieldBar (1 * q)) (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers) :
    ((R.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1), (R.residue₂ ⟨f, h₂⟩ : modularFunctionFieldC k 1))
      ∈ splitTarget q S₀ D₁ D₂ lam := by
  obtain ⟨-, -, -, -, -, -, -, hglue⟩ := hsd
  obtain ⟨hD₁, hD₂, hnode⟩ := hglue f hf h₁ h₂
  exact ⟨hD₁, hD₂, fun s => hnode s s.2 (pow_q_sq_eq_self_of_mem_ssJSet q ((hS₀ s).mp s.2))⟩

omit [IsAlgClosed k] [DecidableEq k] in
theorem frobenius_pow_injective : Function.Injective (fun a : k => a ^ q) := fun a b h => by
  have h' : a ^ q = b ^ q := h
  have : (a - b) ^ q = 0 := by rw [sub_pow_char, h', sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp this)

set_option maxHeartbeats 6400000 in

theorem count_aux
    (S₀ : Finset k) (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k)
    (hlam : ∀ a ∈ S₀, lam a ≠ 0) (hE₁ : -1 ≤ D₁.degree) (hE₂ : -1 ≤ D₂.degree) :
    FiniteDimensional k ↥(splitTarget q S₀ D₁ D₂ lam) ∧
    (Module.finrank k ↥(splitTarget q S₀ D₁ D₂ lam) : ℤ) + min (S₀.card : ℤ) (max D₁.degree D₂.degree + 1)
      ≤ (D₁.degree + 1) + (D₂.degree + 1) := by
  classical
  set T := splitTarget q S₀ D₁ D₂ lam with hT
  have hP1 := AlgebraicCurve.finrank_twistedNodeCompatible_add_min_card_le_of_ringEquiv_ratFunc
    (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
    D₁ D₂ hE₁ hE₂ (fun s : ↥S₀ => (s : k)) (fun s : ↥S₀ => (s : k) ^ q)
    Subtype.val_injective (frobenius_pow_injective.comp Subtype.val_injective)
    (fun s : ↥S₀ => lam s) (fun s => hlam s s.2) T (fun p => mem_splitTarget_iff' p)
  rw [Fintype.card_coe] at hP1
  refine ⟨?_, hP1⟩

  obtain ⟨hfin₁, -⟩ := AlgebraicCurve.finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
    (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c) D₁
  obtain ⟨hfin₂, -⟩ := AlgebraicCurve.finiteDimensional_and_finrank_riemannRochSpace_of_ringEquiv_ratFunc
    (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c) D₂
  let f : T →ₗ[k] (riemannRochSpace D₁) × (riemannRochSpace D₂) :=
    { toFun := fun x => (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2.1⟩)
      map_add' := fun x y => rfl
      map_smul' := fun c x => rfl }
  exact Module.Finite.of_injective f (fun x y h => by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z => ((z.1 : riemannRochSpace D₁) : modularFunctionFieldC k 1)) h
    · exact congrArg (fun z => ((z.2 : riemannRochSpace D₂) : modularFunctionFieldC k 1)) h)

set_option maxHeartbeats 6400000 in

theorem splitTarget_finite_and_finrank_le
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (hdeg₁ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₂.degree) :
    FiniteDimensional k ↥(splitTarget q S₀ D₁ D₂ lam) ∧
    Module.finrank k ↥(splitTarget q S₀ D₁ D₂ lam)
      ≤ Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by
  have hdegE : D₁.degree + D₂.degree = E.degree := hsd.2.1
  have hlam : ∀ a ∈ S₀, lam a ≠ 0 := hsd.2.2.1
  obtain ⟨hfin, hP1⟩ := count_aux (q := q) S₀ D₁ D₂ lam hlam (by omega) (by omega)
  have hcard := LevelOneFibre.genusFF_lt_card_of_ssJSet S₀ hS₀
  have hRR := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar E
  refine ⟨hfin, ?_⟩
  omega

theorem linearIndependent_residuePair_image'
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    {n : ℕ} (Gf : Fin n → modularFunctionFieldBar (1 * q))
    (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers)
    (hGli : LinearIndependent (ResidueField A)
        (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩))) :
    LinearIndependent k (fun j =>
        ((R.ι ((fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) j).1 : modularFunctionFieldC k 1),
         (R.ι ((fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩)) j).2 : modularFunctionFieldC k 1))) :=
  linearIndependent_map_prod_of_coe_eq_coeffMap (n := n)
    (v := fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩))
    R.redBar (modularFunctionFieldFullC (ResidueField A) 1) (modularFunctionFieldC k 1) R.ι R.ι_coe hGli

set_option maxHeartbeats 6400000 in

theorem linearIndependent_residuePair_image
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    {n : ℕ} (Gf : Fin n → modularFunctionFieldBar (1 * q))
    (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers)
    (hGli : LinearIndependent (ResidueField A)
        (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩))) :
    LinearIndependent k (fun j =>
        ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k 1), (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k 1))) := by
  have h := linearIndependent_residuePair_image' R Gf hG₁ hG₂ hGli
  simp only at h
  simp only [LevelOneProlongationPair.residue₁_apply, LevelOneProlongationPair.residue₂_apply]
  exact h

set_option maxHeartbeats 6400000 in

theorem span_residuePair_le_splitTarget
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    {n : ℕ} (Gf : Fin n → modularFunctionFieldBar (1 * q))
    (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers)
    (hGV : ∀ j, Gf j ∈ riemannRochSpace E) :
    Submodule.span k (Set.range fun j =>
        ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k 1), (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k 1)))
      ≤ splitTarget q S₀ D₁ D₂ lam := by
  refine Submodule.span_le.mpr ?_
  rintro p ⟨j, hj⟩
  rw [← hj]
  exact residuePair_mem_splitTarget R S₀ hS₀ E D₁ D₂ lam hsd (Gf j) (hGV j) (hG₁ j) (hG₂ j)

set_option maxHeartbeats 6400000 in

theorem splitTarget_linearIndependent_and_span_eq
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (hdeg₁ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₂.degree)
    (Gf : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) → modularFunctionFieldBar (1 * q))
    (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers)
    (hGV : ∀ j, Gf j ∈ riemannRochSpace E)
    (hGli : LinearIndependent (ResidueField A)
        (fun j => (R.R₁.residue ⟨Gf j, hG₁ j⟩, R.R₂.residue ⟨Gf j, hG₂ j⟩))) :
    LinearIndependent k (fun j =>
        ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k 1), (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k 1))) ∧
    Submodule.span k (Set.range fun j =>
        ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k 1), (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k 1)))
      = splitTarget q S₀ D₁ D₂ lam ∧
    (S₀.card : ℤ) = genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) + 1 := by
  have hdegE : D₁.degree + D₂.degree = E.degree := hsd.2.1
  have hlam : ∀ a ∈ S₀, lam a ≠ 0 := hsd.2.2.1
  obtain ⟨hfin, hP1⟩ := count_aux (q := q) S₀ D₁ D₂ lam hlam (by omega) (by omega)
  have hcard := LevelOneFibre.genusFF_lt_card_of_ssJSet S₀ hS₀
  have hRR := degree_add_one_sub_genusFF_le_finrank_riemannRochSpace_modularFunctionFieldBar E
  haveI := hfin
  have hpli := linearIndependent_residuePair_image R Gf hG₁ hG₂ hGli
  have hle := span_residuePair_le_splitTarget R S₀ hS₀ E D₁ D₂ lam hsd Gf hG₁ hG₂ hGV
  have hspanrk := finrank_span_eq_card hpli
  rw [Fintype.card_fin] at hspanrk
  have hmono := Submodule.finrank_mono hle
  rw [hspanrk] at hmono

  refine ⟨hpli, Submodule.eq_of_le_of_finrank_le hle ?_, ?_⟩
  · rw [hspanrk]
    omega
  · omega

end BetaMain

end FltWs29.C2v3

namespace FltWs29
namespace C2v3

namespace Gamma

p2m_open "AlgebraicCurve~genus"

section Avoid

variable {k₀ K M : Type*} [Field k₀] [Field K] [AddCommGroup M] [Module K M]

def coeffPreimage (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M) (H : Submodule K M) :
    Submodule k₀ (Fin n → k₀) where
  carrier := {μ | (∑ j, σ (μ j) • p j) ∈ H}
  zero_mem' := by
    show (∑ j, σ ((0 : Fin n → k₀) j) • p j) ∈ H
    simp only [Pi.zero_apply, map_zero, zero_smul, Finset.sum_const_zero]
    exact H.zero_mem
  add_mem' := by
    intro μ ν hμ hν
    show (∑ j, σ ((μ + ν) j) • p j) ∈ H
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
    exact H.add_mem hμ hν
  smul_mem' := by
    intro c μ hμ
    show (∑ j, σ ((c • μ) j) • p j) ∈ H
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum]
    exact H.smul_mem _ hμ

theorem mem_coeffPreimage_iff (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M) (H : Submodule K M)
    (μ : Fin n → k₀) : μ ∈ coeffPreimage σ p H ↔ (∑ j, σ (μ j) • p j) ∈ H :=
  Iff.rfl

theorem exists_forall_sum_smul_notMem [Infinite k₀] (σ : k₀ →+* K) {n : ℕ} (p : Fin n → M)
    {ι : Type*} [Finite ι] (H : ι → Submodule K M)
    (hH : ∀ i, ¬ (Submodule.span K (Set.range p) ≤ H i)) :
    ∃ μ : Fin n → k₀, ∀ i, (∑ j, σ (μ j) • p j) ∉ H i := by
  classical
  have hne : ∀ i, coeffPreimage σ p (H i) ≠ ⊤ := by
    intro i htop
    apply hH i
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : (Pi.single j (1 : k₀) : Fin n → k₀) ∈ coeffPreimage σ p (H i) := by
      rw [htop]; exact Submodule.mem_top
    have hsum : (∑ l, σ ((Pi.single j (1 : k₀) : Fin n → k₀) l) • p l) = p j := by
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same, map_one, one_smul]
      · intro l _ hl
        rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have hj' : (∑ l, σ ((Pi.single j (1 : k₀) : Fin n → k₀) l) • p l) ∈ H i := hj
    rw [hsum] at hj'
    exact hj'
  obtain ⟨μ, hμ⟩ :=
    Submodule.exists_forall_notMem_of_forall_ne_top (fun i => coeffPreimage σ p (H i)) hne
  exact ⟨μ, fun i h => hμ i h⟩

end Avoid

section RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem riemannRochSpace_mono {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (Finsupp.le_def.mp h v)).trans h0)

theorem ne_zero_and_ord_add_eq_zero {D : Divisor K F} {f : F} {w : Place K F}
    (hf : f ∈ riemannRochSpace D) (hf' : f ∉ riemannRochSpace (D - Finsupp.single w 1)) :
    f ≠ 0 ∧ w.ord f + D w = 0 := by
  rw [mem_riemannRochSpace_iff] at hf hf'
  push Not at hf'
  obtain ⟨v, hf0, hv⟩ := hf'
  have hvw : v = w := by
    by_contra hne
    have h1 : (D - Finsupp.single w 1 : Divisor K F) v = D v := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hne, sub_zero]
    rcases hf v with h | h
    · exact hf0 h
    · rw [h1] at hv
      exact absurd h (not_le.mpr hv)
  subst hvw
  refine ⟨hf0, ?_⟩
  rcases hf v with h | h
  · exact absurd h hf0
  · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at hv
    omega

theorem hasValue_zero_of_ord_pos (v : Place K F) {f : F} (h : f = 0 ∨ 0 < v.ord f) :
    v.HasValue f 0 := by
  rcases h with rfl | h
  · simpa using Place.hasValue_algebraMap v (0 : K)
  · have hf : f ≠ 0 := by
      rintro rfl
      simp at h
    have hlt : v.adicValuation f < 1 := by
      rw [v.adicValuation_eq_exp_neg_ord hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have hmem : f ∈ v.toValuationSubring := v.mem_iff_adicValuation_le_one.mpr hlt.le
    refine ⟨hmem, ?_⟩
    have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
    rw [map_zero, IsLocalRing.residue_eq_zero_iff]
    exact hmax

theorem not_mem_of_hasValue_twist {D : Divisor K F} {f t : F} {w : Place K F} {c : K}
    (ht0 : t ≠ 0) (ht : w.ord t = 1) (h : w.HasValue (t ^ (D w) * f) c) (hc : c ≠ 0) :
    f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  intro hf
  have hne : t ^ (D w) * f ≠ 0 := h.ne_zero hc
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hne
  have hord := h.ord_eq_zero hc
  rw [w.ord_mul (zpow_ne_zero _ ht0) hf0, w.ord_zpow, ht, mul_one] at hord
  rcases (mem_riemannRochSpace_iff.mp hf) w with h0 | h0
  · exact hf0 h0
  · rw [Finsupp.sub_apply, Finsupp.single_eq_same] at h0
    omega

theorem hasValue_twist_zero_of_mem {D N : Divisor K F} {f t : F} {w : Place K F}
    (ht0 : t ≠ 0) (ht : w.ord t = 1) (hN : 1 ≤ N w) (hf : f ∈ riemannRochSpace (D - N)) :
    w.HasValue (t ^ (D w) * f) 0 := by
  apply hasValue_zero_of_ord_pos
  rcases eq_or_ne f 0 with rfl | hf0
  · left
    rw [mul_zero]
  · right
    rcases (mem_riemannRochSpace_iff.mp hf) w with h0 | h0
    · exact absurd h0 hf0
    · rw [w.ord_mul (zpow_ne_zero _ ht0) hf0, w.ord_zpow, ht, mul_one]
      rw [Finsupp.sub_apply] at h0
      omega

theorem not_mem_sub_single_of_not_mem {D N : Divisor K F} {f : F} {w : Place K F} (hNw : N w = 0)
    (hf : f ∈ riemannRochSpace (D - N)) (hf' : f ∉ riemannRochSpace (D - N - Finsupp.single w 1)) :
    f ∉ riemannRochSpace (D - Finsupp.single w 1) := by
  intro hfw
  apply hf'
  rw [mem_riemannRochSpace_iff] at hf hfw ⊢
  intro v
  by_cases hvw : v = w
  · subst hvw
    rcases hfw v with h | h
    · exact Or.inl h
    · right
      simp only [Finsupp.sub_apply, Finsupp.single_eq_same, hNw] at h ⊢
      omega
  · rcases hf v with h | h
    · exact Or.inl h
    · right
      simp only [Finsupp.sub_apply, Finsupp.single_eq_of_ne hvw] at h ⊢
      omega

theorem hasValue_zero (v : Place K F) : v.HasValue (0 : F) 0 :=
  hasValue_zero_of_ord_pos v (Or.inl rfl)

end RR

end Gamma

end FltWs29.C2v3

namespace FltWs29
namespace C2v3

namespace Gamma

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.PlaceSpecialization Polynomial"

section JLine

variable {k : Type*} [Field k] [DecidableEq k]

theorem algebraMap_X_sub_C (a : k) :
    algebraMap k[X] (RatFunc k) (X - C a) = RatFunc.X - RatFunc.C a := by
  rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

theorem ratFunc_X_sub_C_ne_zero (a : k) : (RatFunc.X - RatFunc.C a : RatFunc k) ≠ 0 := by
  rw [← algebraMap_X_sub_C]
  exact (map_ne_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))).mpr (X_sub_C_ne_zero a)

theorem ord_placeOfPoint_X_sub_C (a b : k) :
    (RationalFunctionField.placeOfPoint k b).ord (RatFunc.X - RatFunc.C a : RatFunc k)
      = if b = a then 1 else 0 := by
  rw [← algebraMap_X_sub_C, RationalFunctionField.ord_placeOfPoint_algebraMap b (X_sub_C_ne_zero a)]
  split_ifs with h
  · subst h
    exact_mod_cast rootMultiplicity_X_sub_C_self
  · rw [Nat.cast_eq_zero]
    refine rootMultiplicity_eq_zero ?_
    rw [IsRoot, eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr h

theorem J_sub_ne_zero (a : k) :
    ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a) ≠ 0 := by
  rw [← ratFuncEquivCharLOneC_X_sub_C k a]
  exact (RingEquiv.map_ne_zero_iff _).mpr (ratFunc_X_sub_C_ne_zero a)

theorem ord_node_J_sub (a b : k) :
    (charLGeomPlaceOfPoint k b).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) a)
      = if b = a then 1 else 0 := by
  rw [← ratFuncEquivCharLOneC_X_sub_C k a]
  exact (Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun c => (ratFuncEquivCharLOneC k).commutes c) (RationalFunctionField.placeOfPoint k b) _).trans
    (ord_placeOfPoint_X_sub_C a b)

end JLine

section JLineClosed

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]

theorem eq_charLGeomPlaceOfPoint_or_eq_placeInfty [DecidableEq (RatFunc k)]
    (v : Place k (modularFunctionFieldC k 1)) :
    (∃ a : k, v = charLGeomPlaceOfPoint k a) ∨
      v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  rcases RationalFunctionField.eq_placeOfPoint_or_eq_placeInfty k ((charLGeomPlaceEquiv k).symm v)
    with ⟨a, ha⟩ | h
  · left
    refine ⟨a, ?_⟩
    rw [← (charLGeomPlaceEquiv k).apply_symm_apply v, ha]
    rfl
  · right
    rw [← (charLGeomPlaceEquiv k).apply_symm_apply v, h]

theorem frob_injective : Function.Injective (fun a : k => a ^ q) := fun a b h => by
  have h' : a ^ q = b ^ q := h
  have : (a - b) ^ q = 0 := by rw [sub_pow_char, h', sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp this)

theorem eq_of_frob_frob_eq [DecidableEq (RatFunc k)]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (v : Place k (modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v) :
    (∃ a : k, a ^ (q ^ 2) = a ∧ v = charLGeomPlaceOfPoint k a) ∨
      v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  rcases eq_charLGeomPlaceOfPoint_or_eq_placeInfty v with ⟨a, rfl⟩ | h
  · left
    refine ⟨a, ?_, rfl⟩
    rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint,
      ← pow_mul, ← sq] at hv
    exact charLGeomPlaceOfPoint_injective k hv
  · exact Or.inr h

theorem pow_q_mem_fixed {a : k} (ha : a ^ (q ^ 2) = a) : (a ^ q) ^ (q ^ 2) = a ^ q := by
  rw [← pow_mul, mul_comm, pow_mul, ha]

noncomputable def nodeDiv₁ (q : ℕ) (S₀ : Finset k) : Divisor k (modularFunctionFieldC k 1) :=
  ∑ s ∈ S₀, Finsupp.single (frobNodePair q s).1 1

noncomputable def nodeDiv₂ (q : ℕ) (S₀ : Finset k) : Divisor k (modularFunctionFieldC k 1) :=
  ∑ s ∈ S₀, Finsupp.single (frobNodePair q s).2 1

theorem frobNodePair_fst_injective : Function.Injective (fun a : k => (frobNodePair q a).1) :=
  fun _ _ h => charLGeomPlaceOfPoint_injective k h

theorem frobNodePair_snd_injective : Function.Injective (fun a : k => (frobNodePair q a).2) :=
  fun _ _ h => frob_injective (q := q) (charLGeomPlaceOfPoint_injective k h)

theorem ord_nodeFst_J_sub (s : k) :
    (frobNodePair q s).1.ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) s) = 1 := by
  rw [frobNodePair_fst, ord_node_J_sub, if_pos rfl]

theorem ord_nodeSnd_J_sub (s : k) :
    (frobNodePair q s).2.ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) - algebraMap k (modularFunctionFieldC k 1) (s ^ q)) = 1 := by
  rw [frobNodePair_snd, ord_node_J_sub, if_pos rfl]

theorem nodeDiv₁_apply_node {S₀ : Finset k} {s : k} (hs : s ∈ S₀) :
    nodeDiv₁ q S₀ (frobNodePair q s).1 = 1 := by
  rw [nodeDiv₁, Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.single_eq_same
  · intro b _ hb
    exact Finsupp.single_eq_of_ne fun h => hb (frobNodePair_fst_injective (q := q) h).symm
  · intro h
    exact absurd hs h

theorem nodeDiv₂_apply_node {S₀ : Finset k} {s : k} (hs : s ∈ S₀) :
    nodeDiv₂ q S₀ (frobNodePair q s).2 = 1 := by
  rw [nodeDiv₂, Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.single_eq_same
  · intro b _ hb
    exact Finsupp.single_eq_of_ne fun h => hb (frobNodePair_snd_injective (q := q) h).symm
  · intro h
    exact absurd hs h

theorem nodeDiv₁_eq_zero_of {S₀ : Finset k} {w : Place k (modularFunctionFieldC k 1)}
    (hw : ∀ s ∈ S₀, (frobNodePair q s).1 ≠ w) : nodeDiv₁ q S₀ w = 0 := by
  rw [nodeDiv₁, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun s hs => Finsupp.single_eq_of_ne fun h => hw s hs h.symm

theorem nodeDiv₂_eq_zero_of {S₀ : Finset k} {w : Place k (modularFunctionFieldC k 1)}
    (hw : ∀ s ∈ S₀, (frobNodePair q s).2 ≠ w) : nodeDiv₂ q S₀ w = 0 := by
  rw [nodeDiv₂, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun s hs => Finsupp.single_eq_of_ne fun h => hw s hs h.symm

theorem nodeDiv₁_nonneg (S₀ : Finset k) : 0 ≤ nodeDiv₁ q S₀ := by
  classical
  rw [Finsupp.le_def]
  intro v
  rw [Finsupp.zero_apply, nodeDiv₁, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun s _ => by
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num

theorem nodeDiv₂_nonneg (S₀ : Finset k) : 0 ≤ nodeDiv₂ q S₀ := by
  classical
  rw [Finsupp.le_def]
  intro v
  rw [Finsupp.zero_apply, nodeDiv₂, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun s _ => by
    rw [Finsupp.single_apply]
    split_ifs <;> norm_num

theorem degree_nodeDiv₁ (S₀ : Finset k) : (nodeDiv₁ q S₀).degree = S₀.card := by
  rw [nodeDiv₁, map_sum]
  simp only [Divisor.degree_single, frobNodePair_fst, deg_charLGeomPlaceOfPoint, Nat.cast_one, mul_one,
    Finset.sum_const, nsmul_eq_mul]

theorem degree_nodeDiv₂ (S₀ : Finset k) : (nodeDiv₂ q S₀).degree = S₀.card := by
  rw [nodeDiv₂, map_sum]
  simp only [Divisor.degree_single, frobNodePair_snd, deg_charLGeomPlaceOfPoint, Nat.cast_one, mul_one,
    Finset.sum_const, nsmul_eq_mul]

theorem exists_mem_splitTarget_fst_not_mem
    (S₀ : Finset k) (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k)
    (hlam : ∀ a ∈ S₀, lam a ≠ 0)
    (hc₁ : (S₀.card : ℤ) ≤ D₁.degree) (hc₂ : (S₀.card : ℤ) ≤ D₂.degree + 1)
    (w : Place k (modularFunctionFieldC k 1)) :
    ∃ p ∈ splitTarget q S₀ D₁ D₂ lam, p.1 ∉ riemannRochSpace (D₁ - Finsupp.single w 1) := by
  classical
  by_cases hw : ∃ s ∈ S₀, (frobNodePair q s).1 = w
  ·
    obtain ⟨s₀, hs₀, rfl⟩ := hw
    let c : ↥S₀ → k := fun s => if (s : k) = s₀ then 1 else 0
    obtain ⟨g₂, hg₂, hv₂⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
        (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        D₂ (by rw [Fintype.card_coe]; omega) (fun s : ↥S₀ => (s : k) ^ q)
        ((frob_injective (q := q)).comp Subtype.val_injective) c
    obtain ⟨g₁, hg₁, hv₁⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
        (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        D₁ (by rw [Fintype.card_coe]; omega) (fun s : ↥S₀ => (s : k))
        Subtype.val_injective (fun s => lam s * c s)
    refine ⟨(g₁, g₂), ⟨hg₁, hg₂, fun s => ⟨c s, ?_, ?_⟩⟩, ?_⟩
    · have h := hv₁ s
      rw [ratFuncEquivCharLOneC_X_sub_C] at h
      exact h
    · have h := hv₂ s
      rw [ratFuncEquivCharLOneC_X_sub_C] at h
      exact h
    · have h := hv₁ ⟨s₀, hs₀⟩
      rw [ratFuncEquivCharLOneC_X_sub_C] at h
      refine not_mem_of_hasValue_twist (J_sub_ne_zero s₀) (ord_nodeFst_J_sub (q := q) s₀) h ?_
      · refine mul_ne_zero (hlam s₀ hs₀) ?_
        show (if ((⟨s₀, hs₀⟩ : ↥S₀) : k) = s₀ then (1 : k) else 0) ≠ 0
        rw [if_pos rfl]
        exact one_ne_zero
  ·
    push Not at hw
    have hN : nodeDiv₁ q S₀ w = 0 := nodeDiv₁_eq_zero_of hw
    obtain ⟨g, hg, hg'⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
        (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        (D₁ - nodeDiv₁ q S₀) (by rw [map_sub, degree_nodeDiv₁]; omega) w
    refine ⟨(g, 0), ⟨riemannRochSpace_mono (sub_le_self _ (nodeDiv₁_nonneg (q := q) S₀)) hg,
      Submodule.zero_mem _, fun s => ⟨0, ?_, ?_⟩⟩, ?_⟩
    · rw [mul_zero]
      exact hasValue_twist_zero_of_mem (J_sub_ne_zero _) (ord_nodeFst_J_sub (q := q) _)
        (le_of_eq (nodeDiv₁_apply_node (q := q) s.2).symm) hg
    · rw [mul_zero]
      exact hasValue_zero _
    · exact not_mem_sub_single_of_not_mem hN hg hg'

theorem exists_mem_splitTarget_snd_not_mem
    (S₀ : Finset k) (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k)
    (hc₁ : (S₀.card : ℤ) ≤ D₁.degree + 1) (hc₂ : (S₀.card : ℤ) ≤ D₂.degree)
    (w : Place k (modularFunctionFieldC k 1)) :
    ∃ p ∈ splitTarget q S₀ D₁ D₂ lam, p.2 ∉ riemannRochSpace (D₂ - Finsupp.single w 1) := by
  classical
  by_cases hw : ∃ s ∈ S₀, (frobNodePair q s).2 = w
  · obtain ⟨s₀, hs₀, rfl⟩ := hw
    let c : ↥S₀ → k := fun s => if (s : k) = s₀ then 1 else 0
    obtain ⟨g₂, hg₂, hv₂⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
        (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        D₂ (by rw [Fintype.card_coe]; omega) (fun s : ↥S₀ => (s : k) ^ q)
        ((frob_injective (q := q)).comp Subtype.val_injective) c
    obtain ⟨g₁, hg₁, hv₁⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_forall_hasValue_zpow_mul_of_ringEquiv_ratFunc
        (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        D₁ (by rw [Fintype.card_coe]; omega) (fun s : ↥S₀ => (s : k))
        Subtype.val_injective (fun s => lam s * c s)
    refine ⟨(g₁, g₂), ⟨hg₁, hg₂, fun s => ⟨c s, ?_, ?_⟩⟩, ?_⟩
    · have h := hv₁ s
      rw [ratFuncEquivCharLOneC_X_sub_C] at h
      exact h
    · have h := hv₂ s
      rw [ratFuncEquivCharLOneC_X_sub_C] at h
      exact h
    · have h := hv₂ ⟨s₀, hs₀⟩
      rw [ratFuncEquivCharLOneC_X_sub_C] at h
      refine not_mem_of_hasValue_twist (J_sub_ne_zero (s₀ ^ q)) (ord_nodeSnd_J_sub (q := q) s₀) h ?_
      · show (if ((⟨s₀, hs₀⟩ : ↥S₀) : k) = s₀ then (1 : k) else 0) ≠ 0
        rw [if_pos rfl]
        exact one_ne_zero
  · push Not at hw
    have hN : nodeDiv₂ q S₀ w = 0 := nodeDiv₂_eq_zero_of hw
    obtain ⟨g, hg, hg'⟩ :=
      AlgebraicCurve.exists_mem_riemannRochSpace_not_mem_sub_single_of_ringEquiv_ratFunc
        (ratFuncEquivCharLOneC k).toRingEquiv (fun c => (ratFuncEquivCharLOneC k).commutes c)
        (D₂ - nodeDiv₂ q S₀) (by rw [map_sub, degree_nodeDiv₂]; omega) w
    refine ⟨(0, g), ⟨Submodule.zero_mem _,
      riemannRochSpace_mono (sub_le_self _ (nodeDiv₂_nonneg (q := q) S₀)) hg, fun s => ⟨0, ?_, ?_⟩⟩, ?_⟩
    · rw [mul_zero, mul_zero]
      exact hasValue_zero _
    · exact hasValue_twist_zero_of_mem (J_sub_ne_zero _) (ord_nodeSnd_J_sub (q := q) _)
        (le_of_eq (nodeDiv₂_apply_node (q := q) s.2).symm) hg
    · exact not_mem_sub_single_of_not_mem hN hg hg'

end JLineClosed

end Gamma

end FltWs29.C2v3

namespace FltWs29
namespace C2v3

namespace Gamma

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.PlaceSpecialization Polynomial"

theorem coeffMap_algebraMap' {R S : Type*} [Field R] [Field S] (σ : R →+* S) (c : R) :
    coeffMap σ (algebraMap R (LaurentSeries R) c) = algebraMap S (LaurentSeries S) (σ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

section Head

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem ι_algebraMap {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) c)
      = algebraMap k (modularFunctionFieldC k 1) (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c)
    = algebraMap k (LaurentSeries k) (R.redBar c)
  exact coeffMap_algebraMap' _ _

theorem ι_smul {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (c : ResidueField A) (x : modularFunctionFieldFullC (ResidueField A) 1) :
    R.ι (c • x) = R.redBar c • R.ι x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ι_algebraMap]

set_option maxHeartbeats 6400000 in

theorem exists_lift {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    {n : ℕ} (Gf : Fin n → modularFunctionFieldBar (1 * q))
    (hG₁ : ∀ j, Gf j ∈ R.R₁.integers) (hG₂ : ∀ j, Gf j ∈ R.R₂.integers)
    (hGV : ∀ j, Gf j ∈ riemannRochSpace E) (μ : Fin n → ResidueField A) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      G ∈ riemannRochSpace E ∧
      R.R₁.residue ⟨G, h₁⟩ = ∑ j, μ j • R.R₁.residue ⟨Gf j, hG₁ j⟩ ∧
      R.R₂.residue ⟨G, h₂⟩ = ∑ j, μ j • R.R₂.residue ⟨Gf j, hG₂ j⟩ := by
  classical
  choose α hα using fun j => IsLocalRing.residue_surjective (μ j)
  have hcmem₁ : ∀ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (α j : AlgebraicClosure ℚ)
      ∈ R.R₁.integers := fun j => (R.R₁.algebraMap_mem_iff _).mpr (α j).2
  have hcmem₂ : ∀ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (α j : AlgebraicClosure ℚ)
      ∈ R.R₂.integers := fun j => (R.R₂.algebraMap_mem_iff _).mpr (α j).2
  set cs₁ : _ → R.R₁.integers := fun j => ⟨_, hcmem₁ j⟩ with hcs₁
  set Gs₁ : _ → R.R₁.integers := fun j => ⟨Gf j, hG₁ j⟩ with hGs₁
  set cs₂ : _ → R.R₂.integers := fun j => ⟨_, hcmem₂ j⟩ with hcs₂
  set Gs₂ : _ → R.R₂.integers := fun j => ⟨Gf j, hG₂ j⟩ with hGs₂
  set x₁ : R.R₁.integers := ∑ j, cs₁ j * Gs₁ j with hx₁
  set x₂ : R.R₂.integers := ∑ j, cs₂ j * Gs₂ j with hx₂
  set G : modularFunctionFieldBar (1 * q) :=
    ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (α j : AlgebraicClosure ℚ) * Gf j
    with hGdef
  have hsum₁ : (x₁ : modularFunctionFieldBar (1 * q)) = G := by
    have e : ((∑ j, cs₁ j * Gs₁ j : R.R₁.integers) : modularFunctionFieldBar (1 * q))
        = ∑ j, ((cs₁ j * Gs₁ j : R.R₁.integers) : modularFunctionFieldBar (1 * q)) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₁, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
    try rfl
  have hsum₂ : (x₂ : modularFunctionFieldBar (1 * q)) = G := by
    have e : ((∑ j, cs₂ j * Gs₂ j : R.R₂.integers) : modularFunctionFieldBar (1 * q))
        = ∑ j, ((cs₂ j * Gs₂ j : R.R₂.integers) : modularFunctionFieldBar (1 * q)) := by
      first
        | exact AddSubmonoidClass.coe_finsetSum _ _
        | exact AddSubmonoidClass.coe_finset_sum _ _
    rw [hx₂, e, hGdef]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MulMemClass.coe_mul]
    try rfl
  have hterm₁ : ∀ j, R.R₁.residue (cs₁ j * Gs₁ j) = μ j • R.R₁.residue ⟨Gf j, hG₁ j⟩ := by
    intro j
    have hc : R.R₁.residue (cs₁ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₁.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have hterm₂ : ∀ j, R.R₂.residue (cs₂ j * Gs₂ j) = μ j • R.R₂.residue ⟨Gf j, hG₂ j⟩ := by
    intro j
    have hc : R.R₂.residue (cs₂ j) = algebraMap (ResidueField A) _ (μ j) := by
      rw [← hα j]
      exact R.R₂.residue_algebraMap (α j)
    rw [map_mul, Algebra.smul_def]
    exact congrArg (· * _) hc
  have h₁ : G ∈ R.R₁.integers := by
    rw [← hsum₁]
    exact x₁.2
  have h₂ : G ∈ R.R₂.integers := by
    rw [← hsum₂]
    exact x₂.2
  have hGx₁ : (⟨G, h₁⟩ : R.R₁.integers) = x₁ := by
    apply Subtype.ext
    exact hsum₁.symm
  have hGx₂ : (⟨G, h₂⟩ : R.R₂.integers) = x₂ := by
    apply Subtype.ext
    exact hsum₂.symm
  refine ⟨G, h₁, h₂, ?_, ?_, ?_⟩
  · rw [hGdef]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hGV j)
  · rw [hGx₁, hx₁, map_sum]
    exact Finset.sum_congr rfl fun j _ => hterm₁ j
  · rw [hGx₂, hx₂, map_sum]
    exact Finset.sum_congr rfl fun j _ => hterm₂ j

noncomputable def phiFixed (q : ℕ) (k : Type*) [Field k] [DecidableEq k] : Finset k :=
  ((X ^ (q ^ 2) - X : k[X]).roots).toFinset

theorem mem_phiFixed {a : k} (ha : a ^ (q ^ 2) = a) : a ∈ phiFixed q k := by
  have hq : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).one_lt
  rw [phiFixed, Multiset.mem_toFinset, Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero k hq),
    Polynomial.IsRoot.def, eval_sub, eval_pow, eval_X, ha, sub_self]

set_option maxHeartbeats 12800000 in

theorem main
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (B : Finset k)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (hdeg₁ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₂.degree) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      R.R₁.residue ⟨G, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨G, h₂⟩ ≠ 0 ∧
      G ∈ riemannRochSpace E ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        v ≠ P.redFst (cuspInftyBar (1 * q)) →
        v.ord (R.residue₁ ⟨G, h₁⟩) + D₁ v = 0 ∧
        (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨G, h₂⟩) +
          D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = 0) ∧
      ((P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨G, h₁⟩) + D₁ (P.redFst (cuspInftyBar (1 * q))) = 0) ∧
      ((P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨G, h₂⟩) + D₂ (P.redSnd (cuspZeroBar (1 * q))) = 0) ∧
      (∀ b ∈ B,
        (charLGeomPlaceOfPoint k b).ord (R.residue₁ ⟨G, h₁⟩) + D₁ (charLGeomPlaceOfPoint k b) = 0 ∧
        (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨G, h₂⟩) + D₂ (charLGeomPlaceOfPoint k b) = 0) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  haveI hfd : FiniteDimensional (AlgebraicClosure ℚ) (riemannRochSpace E) :=
    finiteDimensional_riemannRochSpace_modularFunctionFieldBar E

  obtain ⟨Gf, hG₁, hG₂, hGV, hGli⟩ := alpha_exists_linearIndependent_residuePair R E

  obtain ⟨hli, hspan, hcard⟩ :=
    splitTarget_linearIndependent_and_span_eq R S₀ hS₀ E D₁ D₂ lam hsd hdeg₁ hdeg₂ Gf hG₁ hG₂ hGV hGli
  have hlam : ∀ a ∈ S₀, lam a ≠ 0 := hsd.2.2.1
  have hc₁ : (S₀.card : ℤ) ≤ D₁.degree := by omega
  have hc₂ : (S₀.card : ℤ) ≤ D₂.degree := by omega
  have hc₁' : (S₀.card : ℤ) ≤ D₁.degree + 1 := by omega
  have hc₂' : (S₀.card : ℤ) ≤ D₂.degree + 1 := by omega

  set pv : Fin (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E)) →
      ↥(modularFunctionFieldC k 1) × ↥(modularFunctionFieldC k 1) :=
    fun j => ((R.residue₁ ⟨Gf j, hG₁ j⟩ : modularFunctionFieldC k 1),
      (R.residue₂ ⟨Gf j, hG₂ j⟩ : modularFunctionFieldC k 1)) with hpv

  set pInf : Place k (modularFunctionFieldC k 1) :=
    charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) with hpInf
  set S1 : Finset (Place k (modularFunctionFieldC k 1)) :=
    (phiFixed q k).image (charLGeomPlaceOfPoint k) ∪ {pInf} ∪ B.image (charLGeomPlaceOfPoint k) with hS1
  set S2 : Finset (Place k (modularFunctionFieldC k 1)) := S1 ∪ {P.redSnd (cuspZeroBar (1 * q))} with hS2
  have memS1_fix : ∀ a : k, a ^ (q ^ 2) = a → charLGeomPlaceOfPoint k a ∈ S1 := fun a ha => by
    rw [hS1, Finset.mem_union, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl ⟨a, mem_phiFixed ha, rfl⟩)
  have memS1_inf : pInf ∈ S1 := by
    rw [hS1, Finset.mem_union, Finset.mem_union, Finset.mem_singleton]
    exact Or.inl (Or.inr rfl)
  have memS1_B : ∀ b ∈ B, charLGeomPlaceOfPoint k b ∈ S1 := fun b hb => by
    rw [hS1, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨b, hb, rfl⟩
  have memS2_of : ∀ w ∈ S1, w ∈ S2 := fun w hw => by
    rw [hS2, Finset.mem_union]
    exact Or.inl hw
  have memS2_zero : P.redSnd (cuspZeroBar (1 * q)) ∈ S2 := by
    rw [hS2, Finset.mem_union, Finset.mem_singleton]
    exact Or.inr rfl

  obtain ⟨H, hHdef⟩ :
      ∃ H : ↥S1 ⊕ ↥S2 → Submodule k (↥(modularFunctionFieldC k 1) × ↥(modularFunctionFieldC k 1)),
        H = Sum.elim
          (fun w : ↥S1 => (riemannRochSpace (D₁ - Finsupp.single w.1 1)).comap
            (LinearMap.fst k ↥(modularFunctionFieldC k 1) ↥(modularFunctionFieldC k 1)))
          (fun w : ↥S2 => (riemannRochSpace (D₂ - Finsupp.single w.1 1)).comap
            (LinearMap.snd k ↥(modularFunctionFieldC k 1) ↥(modularFunctionFieldC k 1))) :=
    ⟨_, rfl⟩
  have hH : ∀ i, ¬ (Submodule.span k (Set.range pv) ≤ H i) := by
    rw [hspan]
    rintro (⟨w, hw⟩ | ⟨w, hw⟩) hle
    · obtain ⟨p, hp, hp'⟩ := exists_mem_splitTarget_fst_not_mem (q := q) S₀ D₁ D₂ lam hlam hc₁ hc₂' w
      rw [hHdef, Sum.elim_inl] at hle
      exact hp' (Submodule.mem_comap.mp (hle hp))
    · obtain ⟨p, hp, hp'⟩ := exists_mem_splitTarget_snd_not_mem (q := q) S₀ D₁ D₂ lam hc₁' hc₂ w
      rw [hHdef, Sum.elim_inr] at hle
      exact hp' (Submodule.mem_comap.mp (hle hp))

  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  obtain ⟨μ, hμ⟩ := exists_forall_sum_smul_notMem R.redBar pv H hH

  obtain ⟨G, h₁, h₂, hGE, hres₁, hres₂⟩ := exists_lift R E Gf hG₁ hG₂ hGV μ

  have hy₁ : (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k 1) = (∑ j, R.redBar (μ j) • pv j).1 := by
    rw [Prod.fst_sum]
    simp only [Prod.smul_fst, hpv, LevelOneProlongationPair.residue₁_apply]
    rw [hres₁, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ι_smul]
  have hy₂ : (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k 1) = (∑ j, R.redBar (μ j) • pv j).2 := by
    rw [Prod.snd_sum]
    simp only [Prod.smul_snd, hpv, LevelOneProlongationPair.residue₂_apply]
    rw [hres₂, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ι_smul]
  have hyT : (∑ j, R.redBar (μ j) • pv j) ∈ splitTarget q S₀ D₁ D₂ lam := by
    rw [← hspan]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨hyL₁, hyL₂, -⟩ := (mem_splitTarget_iff (q := q)).mp hyT

  have hR₁ : ∀ w ∈ S1, (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k 1) ≠ 0 ∧
      w.ord (R.residue₁ ⟨G, h₁⟩ : modularFunctionFieldC k 1) + D₁ w = 0 := fun w hw => by
    have h := hμ (Sum.inl ⟨w, hw⟩)
    rw [hHdef, Sum.elim_inl, Submodule.mem_comap, LinearMap.fst_apply] at h
    rw [hy₁]
    exact ne_zero_and_ord_add_eq_zero hyL₁ h
  have hR₂ : ∀ w ∈ S2, (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k 1) ≠ 0 ∧
      w.ord (R.residue₂ ⟨G, h₂⟩ : modularFunctionFieldC k 1) + D₂ w = 0 := fun w hw => by
    have h := hμ (Sum.inr ⟨w, hw⟩)
    rw [hHdef, Sum.elim_inr, Submodule.mem_comap, LinearMap.snd_apply] at h
    rw [hy₂]
    exact ne_zero_and_ord_add_eq_zero hyL₂ h

  have hinf : P.redFst (cuspInftyBar (1 * q)) = pInf := PlaceSpecialization.redFst_cuspInftyBar P
  refine ⟨G, h₁, h₂, ?_, ?_, hGE, ?_, ?_, ?_, ?_⟩
  · intro h0
    apply (hR₁ pInf memS1_inf).1
    rw [LevelOneProlongationPair.residue₁_apply, h0, map_zero]
  · intro h0
    apply (hR₂ _ memS2_zero).1
    rw [LevelOneProlongationPair.residue₂_apply, h0, map_zero]
  · intro v hv _
    rcases eq_of_frob_frob_eq data hKr v hv with ⟨a, ha, rfl⟩ | rfl
    · refine ⟨(hR₁ _ (memS1_fix a ha)).2, ?_⟩
      rw [frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
      exact (hR₂ _ (memS2_of _ (memS1_fix (a ^ q) (pow_q_mem_fixed ha)))).2
    · refine ⟨(hR₁ _ memS1_inf).2, ?_⟩
      rw [frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty]
      exact (hR₂ _ (memS2_of _ memS1_inf)).2
  · rw [hinf]
    exact (hR₁ _ memS1_inf).2
  · exact (hR₂ _ memS2_zero).2
  · intro b hb
    exact ⟨(hR₁ _ (memS1_B b hb)).2, (hR₂ _ (memS2_of _ (memS1_B b hb))).2⟩

end Head

end Gamma

end FltWs29.C2v3

p2m_open "AlgebraicCurve~genus" in open  IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    (R : P.LevelOneProlongationPair)
    (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k)
    (B : Finset k)
    (hB : ∀ b ∈ B, frobOnPlacesGeomLevel k 1 data hKr
      (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k b)) ≠ charLGeomPlaceOfPoint k b)
    (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (D₁ D₂ : Divisor k (modularFunctionFieldC k 1)) (lam : k → k) (hsd : R.SplitDatum S₀ E D₁ D₂ lam)
    (hdeg₁ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₁.degree)
    (hdeg₂ : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) : ℤ) + 1 ≤ D₂.degree) :
    ∃ (G : modularFunctionFieldBar (1 * q)) (h₁ : G ∈ R.R₁.integers) (h₂ : G ∈ R.R₂.integers),
      R.R₁.residue ⟨G, h₁⟩ ≠ 0 ∧ R.R₂.residue ⟨G, h₂⟩ ≠ 0 ∧
      G ∈ riemannRochSpace E ∧
      (∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        v ≠ P.redFst (cuspInftyBar (1 * q)) →
        v.ord (R.residue₁ ⟨G, h₁⟩) + D₁ v = 0 ∧
        (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨G, h₂⟩) +
          D₂ (frobOnPlacesGeomLevel k 1 data hKr v) = 0) ∧
      ((P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨G, h₁⟩) + D₁ (P.redFst (cuspInftyBar (1 * q))) = 0) ∧
      ((P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨G, h₂⟩) + D₂ (P.redSnd (cuspZeroBar (1 * q))) = 0) ∧
      (∀ b ∈ B,
        (charLGeomPlaceOfPoint k b).ord (R.residue₁ ⟨G, h₁⟩) + D₁ (charLGeomPlaceOfPoint k b) = 0 ∧
        (charLGeomPlaceOfPoint k b).ord (R.residue₂ ⟨G, h₂⟩) + D₂ (charLGeomPlaceOfPoint k b) = 0) :=
  FltWs29.C2v3.Gamma.main R S₀ hS₀ B E D₁ D₂ lam hsd hdeg₁ hdeg₂

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_mem_riemannRochSpace_ord_residue_eq_neg_of_splitDatum (solution)
