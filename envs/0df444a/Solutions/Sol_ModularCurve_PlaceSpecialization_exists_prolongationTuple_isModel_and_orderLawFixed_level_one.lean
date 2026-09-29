-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed_level_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0643e073-d51f-51ea-8db9-206569cd63d0

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_of_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_regularityLaw
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized
import Theorems.Thm_ModularCurve_exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_cuspZeroBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_arithFrobC_smul_eq_frobOnPlacesGeomLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ HahnSeries.ramScale_apply ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one.ModularCurve ModularCurve.PlaceSpecialization"

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar qExpand jq ModularPolynomialData modularFunctionFieldFull jqd_mem_full coeffEmb modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence nodePairsOfPlaces ssPlaces jGeomGen coe_jGeomGen jNGeomGen_one IsAffineGeomPlace order_jqModC_def jqModC_ne_zero_def charLGeomPlaceEquiv charLGeomPlaceOfPoint ssJSet arithFrobC IsAtkinLehnerAutFull atkinLehnerInvolutionFull isAtkinLehnerAutFull_atkinLehnerInvolutionFull atkinLehnerInvolutionFull_eq_refl frickeInvolutionBar frickeInvolutionBar_def cuspZeroBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull frickeInvolutionFull_eq_refl cuspInftyBar geomAut PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.jFun PlaceSpecialization.jqFun PlaceSpecialization.tInfty PlaceSpecialization.tZero PlaceSpecialization.IsCuspidal PlaceSpecialization.IsInftySide PlaceSpecialization.IsCuspidal' PlaceSpecialization.IsZeroSide frobNodePair frobNodePair_fst frobNodePair_snd nodePairsOf mem_nodePairsOf_iff placeSpecialization_exists_level_one_of_surjective PlaceSpecialization.LevelOneProlongationPair.exists_isModel PlaceSpecialization.LevelOneProlongationPair.orderLawFixed PlaceSpecialization.LevelOneProlongationPair.regularityLaw pow_q_sq_eq_self_of_mem_ssJSet PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_coe_mem_modularLocalized PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf ssJSet_finite PlaceSpecialization.redFst_eq_placeInfty_of_forall_ord_le_zero PlaceSpecialization.redFst_cuspInftyBar PlaceSpecialization.redSnd_cuspZeroBar PlaceSpecialization.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg ord_charLGeomPlaceEquiv_placeInfty_eq_order frobOnPlacesGeomLevel_charLGeomPlaceOfPoint arithFrobC_smul_eq_frobOnPlacesGeomLevel"
p2m_open "ModularCurve"

theorem mk_qExpand_congr (M : ℕ) {d e : ℕ} [NeZero d] [NeZero e] (hde : d = e)
    (hd : qExpand ℚ d jq ∈ modularFunctionFieldFull M) (he : qExpand ℚ e jq ∈ modularFunctionFieldFull M) :
    (⟨qExpand ℚ d jq, hd⟩ : modularFunctionFieldFull M) = ⟨qExpand ℚ e jq, he⟩ := by
  subst hde
  rfl

theorem algEquiv_modularFunctionFieldFull_ext (M : ℕ)
    (σ τ : modularFunctionFieldFull M ≃ₐ[ℚ] modularFunctionFieldFull M)
    (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ M),
      σ ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩ = τ ⟨qExpand ℚ d jq, jqd_mem_full M hd⟩) :
    σ = τ := by
  apply AlgEquiv.ext
  rintro ⟨x, hx⟩
  suffices hmain : ∀ (y : LaurentSeries ℚ) (hy : y ∈ modularFunctionFieldFull M),
      ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) = (τ ⟨y, hy⟩ : modularFunctionFieldFull M) from
    Subtype.ext (hmain x hx)
  intro y hy
  induction hy using IntermediateField.adjoin_induction with
  | mem y hy =>
    obtain ⟨d, hd0, hdM, rfl⟩ := hy
    exact congrArg Subtype.val (h d hd0 hdM)
  | algebraMap r =>

    have e : (⟨_, IntermediateField.algebraMap_mem (modularFunctionFieldFull M) r⟩ : modularFunctionFieldFull M)
        = ((r : ℚ) : modularFunctionFieldFull M) := by
      apply Subtype.ext
      rw [SubfieldClass.coe_ratCast]
      exact eq_ratCast _ r
    rw [e, map_ratCast, map_ratCast]
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, add_mem hy hz⟩ : modularFunctionFieldFull M) = ⟨y, hy⟩ + ⟨z, hz⟩ := rfl
    rw [e, map_add, map_add]
    show ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) + (σ ⟨z, hz⟩ : modularFunctionFieldFull M)
      = ((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) + (τ ⟨z, hz⟩ : modularFunctionFieldFull M)
    rw [ihy, ihz]
  | inv y hy ihy =>
    have e : (⟨y⁻¹, inv_mem hy⟩ : modularFunctionFieldFull M) = (⟨y, hy⟩ : modularFunctionFieldFull M)⁻¹ := rfl
    rw [e, map_inv₀, map_inv₀]
    show (((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ))⁻¹
      = (((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ))⁻¹
    rw [ihy]
  | mul y z hy hz ihy ihz =>
    have e : (⟨y * z, mul_mem hy hz⟩ : modularFunctionFieldFull M) = ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
    rw [e, map_mul, map_mul]
    show ((σ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) * (σ ⟨z, hz⟩ : modularFunctionFieldFull M)
      = ((τ ⟨y, hy⟩ : modularFunctionFieldFull M) : LaurentSeries ℚ) * (τ ⟨z, hz⟩ : modularFunctionFieldFull M)
    rw [ihy, ihz]

theorem isAtkinLehnerAutFull_one_iff (q : ℕ) [Fact q.Prime]
    (σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)) :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    IsAtkinLehnerAutFull 1 q σ ↔ IsFrickeAutFull (1 * q) σ := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  constructor
  · intro hAL a b hab ha hb
    obtain ⟨h1, h2⟩ := hAL 1 inferInstance (dvd_refl 1)

    have ha' : a ∣ q := ⟨b, by omega⟩
    rcases (Nat.dvd_prime hq).mp ha' with ha1 | haq
    · have hb' : b = 1 * q := by rw [ha1] at hab; omega
      rw [mk_qExpand_congr (1 * q) ha1 _ (jqd_mem_full (1 * q) (one_dvd _)),
        mk_qExpand_congr (1 * q) hb' _ (jqd_mem_full (1 * q) (dvd_refl _))]
      exact h1
    · have hb' : b = 1 := by
        have : q * b = q * 1 := by rw [haq] at hab; rw [mul_one, hab, one_mul]
        exact Nat.eq_of_mul_eq_mul_left hq.pos this
      rw [mk_qExpand_congr (1 * q) (haq.trans (one_mul q).symm) _ (jqd_mem_full (1 * q) (dvd_refl _)),
        mk_qExpand_congr (1 * q) hb' _ (jqd_mem_full (1 * q) (one_dvd _))]
      exact h2
  · intro hF d hd0 hd
    obtain rfl : d = 1 := Nat.dvd_one.mp hd
    constructor
    · exact hF 1 (1 * q) (by ring) inferInstance inferInstance
    · exact hF (1 * q) 1 (by ring) inferInstance inferInstance

theorem atkinLehnerInvolutionFull_one (q : ℕ) [Fact q.Prime] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    atkinLehnerInvolutionFull 1 q = frickeInvolutionFull (1 * q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hq : q.Prime := Fact.out
  by_cases hex : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
      IsFrickeAutFull (1 * q) σ
  · have hex' : ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
        IsAtkinLehnerAutFull 1 q σ := by
      obtain ⟨σ, hσ⟩ := hex
      exact ⟨σ, (isAtkinLehnerAutFull_one_iff q σ).mpr hσ⟩
    have h1 := (isAtkinLehnerAutFull_one_iff q _).mp (isAtkinLehnerAutFull_atkinLehnerInvolutionFull 1 q hex')
    have h2 := isFrickeAutFull_frickeInvolutionFull (1 * q) hex
    apply algEquiv_modularFunctionFieldFull_ext
    intro d hd0 hd
    have hd' : d ∣ q := by rwa [one_mul] at hd
    rcases (Nat.dvd_prime hq).mp hd' with hd1 | hdq
    · have e1 := h1 1 (1 * q) (by ring) inferInstance inferInstance
      have e2 := h2 1 (1 * q) (by ring) inferInstance inferInstance
      rw [mk_qExpand_congr (1 * q) hd1 _ (jqd_mem_full (1 * q) (one_dvd _))]
      exact e1.trans e2.symm
    · have e1 := h1 (1 * q) 1 (by ring) inferInstance inferInstance
      have e2 := h2 (1 * q) 1 (by ring) inferInstance inferInstance
      rw [mk_qExpand_congr (1 * q) (hdq.trans (one_mul q).symm) _ (jqd_mem_full (1 * q) (dvd_refl _))]
      exact e1.trans e2.symm
  · have hex' : ¬ ∃ σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q),
        IsAtkinLehnerAutFull 1 q σ := fun ⟨σ, hσ⟩ => hex ⟨σ, (isAtkinLehnerAutFull_one_iff q σ).mp hσ⟩
    rw [atkinLehnerInvolutionFull_eq_refl 1 q hex', frickeInvolutionFull_eq_refl (1 * q) hex]

theorem atkinLehnerBar_one (q : ℕ) [Fact q.Prime] :
    haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
    ProlongationTuple.atkinLehnerBar 1 q = frickeInvolutionBar (1 * q) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  show geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)) (atkinLehnerInvolutionFull 1 q) = _
  rw [frickeInvolutionBar_def, atkinLehnerInvolutionFull_one]

end ModularCurve

namespace LT1

p2m_open "ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one.ModularCurve ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem mkBar_qExpand_congr (M : ℕ) {d e : ℕ} [NeZero d] [NeZero e] (hde : d = e)
    (hd : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq) ∈ modularFunctionFieldBar M)
    (he : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ e jq) ∈ modularFunctionFieldBar M) :
    (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ d jq), hd⟩ : modularFunctionFieldBar M)
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ e jq), he⟩ := by
  subst hde
  rfl

theorem jQFun_one : ProlongationTuple.jQFun 1 q = PlaceSpecialization.jqFun (q := q) := by
  unfold ProlongationTuple.jQFun PlaceSpecialization.jqFun
  exact mkBar_qExpand_congr (1 * q) (one_mul q).symm _ _

theorem jFun_one : ProlongationTuple.jFun 1 q = PlaceSpecialization.jFun (q := q) := rfl

theorem tInfty_one : ProlongationTuple.tInfty 1 q = PlaceSpecialization.tInfty (q := q) := by
  unfold ProlongationTuple.tInfty PlaceSpecialization.tInfty
  rw [jQFun_one, jFun_one]
  exact (congrArg (fun n : ℕ => PlaceSpecialization.jqFun (q := q) / PlaceSpecialization.jFun (q := q) ^ n)
    (one_mul q)).symm

theorem tZero_one : ProlongationTuple.tZero 1 q = PlaceSpecialization.tZero (q := q) := by
  unfold ProlongationTuple.tZero PlaceSpecialization.tZero
  rw [jQFun_one, jFun_one]
  exact (congrArg (fun n : ℕ => PlaceSpecialization.jFun (q := q) / PlaceSpecialization.jqFun (q := q) ^ n)
    (one_mul q)).symm

theorem isInftySide_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    ProlongationTuple.IsInftySide P = P.IsInftySide := by
  funext W
  unfold ProlongationTuple.IsInftySide PlaceSpecialization.IsInftySide
    ProlongationTuple.IsCuspidal PlaceSpecialization.IsCuspidal
  rw [tInfty_one, jFun_one]

theorem isZeroSide_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    ProlongationTuple.IsZeroSide P = P.IsZeroSide := by
  funext W
  unfold ProlongationTuple.IsZeroSide PlaceSpecialization.IsZeroSide
    ProlongationTuple.IsCuspidal' PlaceSpecialization.IsCuspidal'
  rw [tZero_one, jQFun_one]

theorem reduceFst_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : P.reduceFst W = P.redFst W := rfl

theorem reduceSnd_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) : P.reduceSnd W = P.redSnd W := rfl

theorem isStrictFst_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.IsStrictFst = P.IsStrictTypeOne := rfl

theorem isStrictSnd_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.IsStrictSnd = P.IsStrictTypeTwo := rfl

theorem eq_cusp_of_not_isAffineGeomPlace [DecidableEq (RatFunc k)]
    {v : Place k (modularFunctionFieldC k 1)} (hv : ¬ IsAffineGeomPlace k 1 v) :
    v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  apply ModularCurve.eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
  by_contra h
  push Not at h
  apply hv
  have hmem : (jGeomGen k 1 : modularFunctionFieldC k 1) ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg (by
      intro h0
      exact jqModC_ne_zero_def k (congrArg Subtype.val h0)) h
  refine ⟨hmem, ?_⟩
  rw [jNGeomGen_one]
  exact hmem

theorem ne_cusp_of_isAffineGeomPlace [DecidableEq (RatFunc k)]
    {v : Place k (modularFunctionFieldC k 1)} (hv : IsAffineGeomPlace k 1 v) :
    v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
  intro h
  have h0 := v.ord_nonneg_of_mem hv.1
  rw [h, ModularCurve.ord_charLGeomPlaceEquiv_placeInfty_eq_order] at h0
  have : ((jGeomGen k 1 : modularFunctionFieldC k 1) : LaurentSeries k).order = -1 := by
    rw [coe_jGeomGen]; exact order_jqModC_def k
  rw [this] at h0
  exact absurd h0 (by norm_num)

end LT1

set_option maxHeartbeats 6400000 in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one.ModularCurve ModularCurve.PlaceSpecialization LT1 in
theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} [IsAlgClosed k]
    [DecidableEq k]
    (hred : Function.Surjective red)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k) :
    ∃ P₁ : PlaceSpecialization A q 1 data hKr k red hα hβ,
      ∃ R : ProlongationTuple P₁, R.IsModel ∧ R.RegularityLaw W ∧ R.NodeValueLaw W ∧ R.OrderLawFixed := by
  classical

  obtain ⟨P⟩ := ModularCurve.placeSpecialization_exists_level_one_of_surjective q data hKr A k red hred hα hβ
  obtain ⟨R', hM'⟩ := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_isModel P
  have hO' := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.orderLawFixed R'
  set S₀ : Finset k := (ModularCurve.ssJSet_finite q k).toFinset with hS₀def
  have hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k := fun a => Set.Finite.mem_toFinset _
  have hRL' := ModularCurve.PlaceSpecialization.LevelOneProlongationPair.regularityLaw R'
    (S₀ := S₀) (fun a ha => (hS₀ a).mp ha)

  obtain ⟨W', hW', hnodes'⟩ := ModularCurve.exists_nodePairsOfPlaces_arithFrobC_eq_nodePairsOf q k S₀ hS₀
  have hWW' : W = W' := Finset.ext fun w => (hW w).trans (hW' w).symm
  have hnodes : nodePairsOfPlaces (arithFrobC q k 1) W = nodePairsOf q S₀ := by rw [hWW']; exact hnodes'

  have hw : ∀ f : modularFunctionFieldBar (1 * q),
      ProlongationTuple.atkinLehnerBar 1 q f = frickeInvolutionBar (1 * q) f := fun f => by
    rw [ModularCurve.atkinLehnerBar_one]
  let R : ProlongationTuple P :=
    { redBar := R'.redBar
      redBar_residue := R'.redBar_residue
      ι := R'.ι
      ι_coe := R'.ι_coe
      R₁ := R'.R₁
      R₂ := R'.R₂
      residue₁_coeffMap := R'.residue₁_coeffMap
      mem_integersFst_iff := fun f =>
        ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersFst_iff_coe_mem_modularLocalized R' f
      mem_integersSnd_iff := fun f => by
        rw [hw]
        exact ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_iff_coe_frickeInvolutionBar_mem_modularLocalized R' f
      residue₂_eq := fun f h => by
        rw [R'.residue₂_eq f h]
        congr 1
        exact Subtype.ext (hw f).symm
      residue₁_eq_modularRedLocHom := R'.residue₁_eq_modularRedLocHom }
  have hres₁ : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R.R₁.integers),
      R.residue₁ ⟨f, h⟩ = R'.residue₁ ⟨f, h⟩ := fun _ _ => rfl
  have hres₂ : ∀ (f : modularFunctionFieldBar (1 * q)) (h : f ∈ R.R₂.integers),
      R.residue₂ ⟨f, h⟩ = R'.residue₂ ⟨f, h⟩ := fun _ _ => rfl

  have hcusp₁ : P.redFst (cuspInftyBar (1 * q)) = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) :=
    ModularCurve.PlaceSpecialization.redFst_cuspInftyBar P
  have hcusp₂ : P.redSnd (cuspZeroBar (1 * q)) = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) :=
    ModularCurve.PlaceSpecialization.redSnd_cuspZeroBar P
  refine ⟨P, R, ⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  ·
    intro f h₁ h₂ hr₁ hr₂ D hD v hv
    exact hM'.1 f h₁ h₂ hr₁ hr₂ D hD v hv
  ·
    intro f h₁ h₂ hr₁ hr₂ D hD v hv
    exact hM'.2.1 f h₁ h₂ hr₁ hr₂ D hD v hv
  ·
    intro f h₁ h₂ hr₁ hr₂ D hD c hc
    rw [isInftySide_eq] at hc ⊢
    have hc1 : P.reduceFst c = P.redFst (cuspInftyBar (1 * q)) := by
      rw [reduceFst_eq, hcusp₁]
      exact ModularCurve.PlaceSpecialization.redFst_eq_placeInfty_of_forall_ord_le_zero P c hc.1
    rw [hc1]
    exact hM'.2.2.1 f h₁ h₂ hr₁ hr₂ D hD
  ·
    intro f h₁ h₂ hr₁ hr₂ D hD c hc
    have hnaff : ¬ IsAffineGeomPlace k 1 (P.reduceSnd c) := by
      intro haff
      obtain ⟨a, ha, -⟩ :=
        ModularCurve.PlaceSpecialization.exists_ord_jQFun_sub_pos_of_isAffineGeomPlace_reduceSnd P c haff
      exact absurd (hc.1 a) (not_le.mpr ha)
    have hc2 : P.reduceSnd c = P.redSnd (cuspZeroBar (1 * q)) := by
      rw [hcusp₂]; exact eq_cusp_of_not_isAffineGeomPlace hnaff
    rw [isZeroSide_eq] at hc ⊢
    rw [hc2]
    exact hM'.2.2.2 f h₁ h₂ hr₁ hr₂ D hD
  ·
    intro f h₁ h₂ v hv haff hreg
    exact hRL'.1 f h₁ h₂ v hv (by rw [hcusp₁]; exact ne_cusp_of_isAffineGeomPlace haff) hreg
  ·
    intro f h₁ h₂ s hs hreg
    rw [hnodes, ModularCurve.mem_nodePairsOf_iff] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    have ha' : a ∈ ssJSet q k := (hS₀ a).mp ha
    exact hRL'.2 f h₁ h₂ a ha (ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha') hreg
  ·
    intro f h₁ h₂ hr₁ hr₂ s hs hsupp
    rw [hnodes, ModularCurve.mem_nodePairsOf_iff] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    have ha' : a ∈ ssJSet q k := (hS₀ a).mp ha
    have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha'

    have hφ : ∀ b : k, frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k b)
        = charLGeomPlaceOfPoint k (b ^ q) := fun b =>
      ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr b
    have hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr
        (charLGeomPlaceOfPoint k a)) = charLGeomPlaceOfPoint k a := by
      rw [hφ, hφ, ← pow_mul, ← pow_two, ha2]

    have hover : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        P.reduceFst V = (frobNodePair q a).1 → P.reduceSnd V = (frobNodePair q a).2 := by
      intro V hV
      rw [frobNodePair_fst] at hV
      rw [frobNodePair_snd, ← hφ]
      rcases P.d1 V with h | h
      ·
        change P.reduceFst V = frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V) at h
        have h2 : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V))
            = frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) := by rw [h]

        have hinj : Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) := by
          intro x y hxy
          rw [← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr,
            ← ModularCurve.arithFrobC_smul_eq_frobOnPlacesGeomLevel q k 1 data hKr] at hxy
          exact smul_left_cancel _ hxy

        have hfixV : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V))
            = P.reduceFst V := by rw [hV]; exact hfix
        have h3 : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceSnd V))
            = P.reduceSnd V := by
          apply hinj
          rw [← h]
          exact hfixV

        rw [← hV, h, h3]
      · change frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst V) = P.reduceSnd V at h
        rw [← h, hV]
    have hnopole : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        P.reduceFst V = (frobNodePair q a).1 → V.ord f = 0 := by
      intro V hV
      by_contra hne
      exact hsupp V hne ⟨hV, hover V hV⟩

    have hu₁ : IsUnit (⟨f, h₁⟩ : R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero (by
      intro h0; apply hr₁; show R.ι (R.R₁.residue ⟨f, h₁⟩) = 0; rw [h0, map_zero])
    have hu₂ : IsUnit (⟨f, h₂⟩ : R.R₂.integers) := R.R₂.isUnit_of_residue_ne_zero (by
      intro h0; apply hr₂; show R.ι (R.R₂.residue ⟨f, h₂⟩) = 0; rw [h0, map_zero])
    have hf0 : f ≠ 0 := by
      rintro rfl; apply hr₁
      have : (⟨(0 : modularFunctionFieldBar (1 * q)), h₁⟩ : R.R₁.integers) = 0 := rfl
      rw [this, map_zero]
    have hinv₁ : f⁻¹ ∈ R.R₁.integers := by
      obtain ⟨u, hu⟩ := hu₁
      have : ((u⁻¹ : R.R₁.integersˣ) : R.R₁.integers).1 = f⁻¹ := by
        have h := congrArg Subtype.val (u.inv_mul)
        rw [hu] at h
        change ((u⁻¹ : R.R₁.integersˣ) : R.R₁.integers).1 * f = 1 at h
        exact (eq_inv_of_mul_eq_one_left h)
      rw [← this]; exact SetLike.coe_mem _
    have hinv₂ : f⁻¹ ∈ R.R₂.integers := by
      obtain ⟨u, hu⟩ := hu₂
      have : ((u⁻¹ : R.R₂.integersˣ) : R.R₂.integers).1 = f⁻¹ := by
        have h := congrArg Subtype.val (u.inv_mul)
        rw [hu] at h
        change ((u⁻¹ : R.R₂.integersˣ) : R.R₂.integers).1 * f = 1 at h
        exact (eq_inv_of_mul_eq_one_left h)
      rw [← this]; exact SetLike.coe_mem _

    have hregf : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        P.redFst V = (frobNodePair q a).1 → 0 ≤ V.ord f := fun V hV => (hnopole V hV).ge
    have hregi : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
        P.redFst V = (frobNodePair q a).1 → 0 ≤ V.ord f⁻¹ := fun V hV => by
      rw [V.ord_inv, hnopole V hV, neg_zero]
    obtain ⟨c, hc₁, hc₂⟩ := hRL'.2 f h₁ h₂ a ha ha2 hregf
    obtain ⟨c', hc₁', hc₂'⟩ := hRL'.2 f⁻¹ hinv₁ hinv₂ a ha ha2 hregi

    have hprod₁ : (R'.residue₁ ⟨f, h₁⟩ : modularFunctionFieldC k 1) * R'.residue₁ ⟨f⁻¹, hinv₁⟩ = 1 := by
      rw [← map_mul, ← map_one R'.residue₁]
      congr 1
      apply Subtype.ext
      change f * f⁻¹ = 1
      exact mul_inv_cancel₀ hf0
    have hcc' : c * c' = 1 := by
      have h1 := hc₁.mul hc₁'
      rw [hprod₁] at h1
      exact h1.unique (frobNodePair q a).1.hasValue_one
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, zero_mul] at hcc'; exact zero_ne_one hcc'
    exact ⟨c, hc0, hc₁, hc₂⟩
  ·
    intro f h₁ h₂ hr₁ hr₂ D hD v hv haff
    exact hO' f h₁ h₂ hr₁ hr₂ D hD v hv (by rw [hcusp₁]; exact ne_cusp_of_isAffineGeomPlace haff)

end S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed_level_one (solution)
