-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.splitDatum_of_forall_centred_ord_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/83c2a12c-3616-555a-8d93-e438ccbbb12e

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplit
import Definitions.Def_ModularCurve_LevelOneProlongationPairRegularity
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_LevelOneProlongationPairSplitEff
import Definitions.Def_ModularCurve_ArithmeticGalois
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_le_ord_residue_and_exists_hasValue_of_mul
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawZero_oneSided
import Theorems.Thm_ModularCurve_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictTypeOne_or_isStrictTypeTwo_iff_ne
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_finiteDimensional_riemannRochSpace_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceEquiv_placeInfty_of_ord_neg
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_PlaceSpecialization_eq_of_isInftySide_of_hasValue_jFun
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
set_option autoImplicit false
set_option Elab.async false

set_option synthInstance.maxHeartbeats 1600000

namespace FltWs24
namespace N3

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ord_charLGeomPlaceOfPoint_jqModC_sub (k : Type*) [Field k] (b : k) :
    (charLGeomPlaceOfPoint k b).ord
      ((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) b) = 1 := by

  set e : RatFunc k ≃+* ↥(modularFunctionFieldC k 1) := (ratFuncEquivCharLOneC k).toRingEquiv with he_def
  have he : ∀ c : k, e (algebraMap k (RatFunc k) c) = algebraMap k ↥(modularFunctionFieldC k 1) c :=
    fun c => (ratFuncEquivCharLOneC k).commutes c
  have hplace : charLGeomPlaceOfPoint k b = Place.congrRingEquiv e he (RationalFunctionField.placeOfPoint k b) := rfl
  have hX : e RatFunc.X = (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) := by
    apply Subtype.ext
    rw [he_def]
    show ((ratFuncEquivCharLOneC k RatFunc.X : ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = jqModC k
    unfold ratFuncEquivCharLOneC
    rw [AlgEquiv.trans_apply]
    first
      | exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)
      | (rw [IntermediateField.equivOfEq_apply]
         exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k))
      | (rw [← RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)]
         rfl)
  have helem : (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) b
      = e (algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C b)) := by
    rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub, hX, ← he b, RatFunc.algebraMap_eq_C]
  rw [hplace, helem, Place.ord_congrRingEquiv,
    RationalFunctionField.ord_placeOfPoint_algebraMap b (Polynomial.X_sub_C_ne_zero b),
    Polynomial.rootMultiplicity_X_sub_C_self]
  simp

end FltWs24.N3

set_option autoImplicit false

namespace FltWs24
namespace PlaceDict

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
  {red : A →+* k} {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

omit [IsAlgClosed k] [DecidableEq k] in
theorem frickeInvolutionBar_mul_self :
    frickeInvolutionBar (1 * q) * frickeInvolutionBar (1 * q) = 1 := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  refine AlgEquiv.ext fun y => ?_
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  exact frickeInvolutionBar_frickeInvolutionBar (1 * q) y

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_redFst_cuspInftyBar (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    frobOnPlacesGeomLevel k 1 data hKr (P.redFst (cuspInftyBar (1 * q))) = P.redFst (cuspInftyBar (1 * q)) := by
  classical
  rw [redFst_cuspInftyBar P]
  exact frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr

omit [IsAlgClosed k] [DecidableEq k] in
theorem redSnd_cuspZeroBar_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ) :
    P.redSnd (cuspZeroBar (1 * q)) = P.redFst (cuspInftyBar (1 * q)) := by
  rw [← redFst_frickeInvolutionBar_smul P, cuspZeroBar_def, smul_smul, frickeInvolutionBar_mul_self, one_smul]

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 3200000 in
theorem frobNodePair_fst_ne_cusp (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (a : k) :
    (frobNodePair q a).1 ≠ P.redFst (cuspInftyBar (1 * q)) := by
  classical
  intro h
  rw [frobNodePair_fst, redFst_cuspInftyBar P] at h

  set jt : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩ with hjt
  have hneg : (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord jt < 0 := by
    rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order]
    have h1 : (jt : LaurentSeries k).order ≤ -1 :=
      HahnSeries.order_le_of_coeff_ne_zero (by
        show (jqModC k).coeff (-1) ≠ 0
        rw [coeff_jqModC_neg_one]; exact one_ne_zero)
    omega
  have hpos : 0 ≤ (charLGeomPlaceOfPoint k a).ord jt := by
    have hJ : 0 ≤ (charLGeomPlaceOfPoint k a).ord (jt - algebraMap k _ a) := by
      rw [FltWs24.N3.ord_charLGeomPlaceOfPoint_jqModC_sub k a]; exact zero_le_one
    have hmemJ : jt - algebraMap k _ a ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := by
      by_cases h0 : jt - algebraMap k _ a = 0
      · rw [h0]; exact zero_mem _
      · exact Place.mem_of_ord_nonneg _ h0 hJ
    have hmem : jt ∈ (charLGeomPlaceOfPoint k a).toValuationSubring := by
      have : jt = (jt - algebraMap k _ a) + algebraMap k _ a := by ring
      rw [this]
      exact add_mem hmemJ ((charLGeomPlaceOfPoint k a).algebraMap_mem' a)
    exact Place.ord_nonneg_of_mem _ hmem
  rw [h] at hpos
  omega

omit [IsAlgClosed k] [DecidableEq k] in
theorem redFst_eq_of_isCuspidal (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsCuspidal W) :
    P.redFst W = P.redFst (cuspInftyBar (1 * q)) := by
  classical
  rw [redFst_cuspInftyBar P]
  exact redFst_eq_placeInfty_of_forall_ord_le_zero P W hW

omit [IsAlgClosed k] [DecidableEq k] in
theorem isCuspidal_of_redFst_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
    (hW : P.redFst W = P.redFst (cuspInftyBar (1 * q))) : P.IsCuspidal W := by
  intro a
  by_contra hlt
  push_neg at hlt
  have h := (redFst_eq_charLGeomPlaceOfPoint_iff P W (red a)).mpr ⟨a, rfl, hlt⟩
  rw [hW] at h
  exact frobNodePair_fst_ne_cusp P (red a) (by rw [frobNodePair_fst]; exact h.symm)

omit [IsAlgClosed k] [DecidableEq k] in
theorem isCuspidal_of_isZeroSide (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsZeroSide W) :
    P.IsCuspidal W := by
  intro a
  by_contra hlt
  push_neg at hlt
  obtain ⟨y, hy⟩ := exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos P W a hlt
  have := hW.1 y
  exact absurd hy (not_lt.mpr this)

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 3200000 in
theorem redSnd_eq_of_isZeroSide (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (hW : P.IsZeroSide W) :
    P.redSnd W = P.redSnd (cuspZeroBar (1 * q)) := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  rw [redSnd_cuspZeroBar_eq, ← redFst_frickeInvolutionBar_smul P W]
  apply redFst_eq_of_isCuspidal

  intro a
  have key : ∀ (n : ℕ) [NeZero n], n = q → IsFrickeAutFull n (frickeInvolutionFull n) := by
    rintro n _ rfl; exact isFrickeAutFull_frickeInvolutionFull_prime _
  have hFA : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) := key (1 * q) (one_mul q)
  have h0 := frickeInvolutionBar_coeffEmb_qExpand (1 * q) hFA (1 * q) 1 (mul_one _)
  have hwj : frickeInvolutionBar (1 * q) (PlaceSpecialization.jqFun (q := q)) = PlaceSpecialization.jFun (q := q) :=
    h0.trans (Subtype.ext (by
      show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq) = coeffEmb (AlgebraicClosure ℚ) jq
      rw [qExpand_one_apply]))
  have htrans : PlaceSpecialization.jFun (q := q) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)
      = frickeInvolutionBar (1 * q) (PlaceSpecialization.jqFun (q := q)
          - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) := by
    rw [map_sub, hwj, AlgEquiv.commutes]
  show (frickeInvolutionBar (1 * q) • W).ord (PlaceSpecialization.jFun (q := q) - _) ≤ 0
  rw [htrans, Place.ord_smul]
  exact hW.1 a

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 3200000 in
theorem redFst_eq_frobNodePair_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (a : k) (ha2 : a ^ (q ^ 2) = a) :
    P.redFst W = (frobNodePair q a).1 ↔
      ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  rw [frobNodePair_fst]
  constructor
  · intro h
    obtain ⟨x, hx, hxord⟩ := (redFst_eq_charLGeomPlaceOfPoint_iff P W a).mp h
    refine ⟨⟨x, hx, hxord⟩, ?_⟩
    obtain ⟨y, hy⟩ := exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos P W x hxord
    refine ⟨y, ?_, hy⟩

    have hbridge : heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
        = PlaceSpecialization.jqFun (q := q) := by
      apply Subtype.ext
      rw [coe_heckeBetaBar]
      show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
      have e1 : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
          = qExpand (AlgebraicClosure ℚ) (1 * q) (coeffEmb (AlgebraicClosure ℚ) jq) := coeffMap_qExpand _ _ _
      rw [e1]
      have hgen : ∀ (n : ℕ) [NeZero n], n = q →
          qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq)
            = qExpand (AlgebraicClosure ℚ) n (coeffEmb (AlgebraicClosure ℚ) jq) := by
        rintro n _ rfl; rfl
      exact hgen (1 * q) (one_mul q)
    have hy' := hy
    rw [← hbridge] at hy'
    have hsnd := redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos P W y hy'
    rcases P.d1 W with h1 | h1
    ·
      change P.redFst W = frobOnPlacesGeomLevel k 1 data hKr (P.redSnd W) at h1
      rw [h, hsnd, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint] at h1
      have ha : a = red y ^ q := charLGeomPlaceOfPoint_injective k h1

      have hfrob : Function.Injective (frobenius k q) := frobenius_inj k q
      have hy2 : red y ^ (q ^ 2) = red y := by
        apply hfrob
        show (red y ^ (q ^ 2)) ^ q = (red y) ^ q
        rw [← ha, ← pow_mul, show q ^ 2 * q = q * (q ^ 2) by ring, pow_mul, ← ha, ha2]
      rw [ha, ← pow_mul, show q * q = q ^ 2 by ring, hy2]
    · change frobOnPlacesGeomLevel k 1 data hKr (P.redFst W) = P.redSnd W at h1
      rw [h, hsnd, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint] at h1
      exact (charLGeomPlaceOfPoint_injective k h1).symm
  · rintro ⟨⟨x, hx, hxord⟩, -⟩
    exact (redFst_eq_charLGeomPlaceOfPoint_iff P W a).mpr ⟨x, hx, hxord⟩

end FltWs24.PlaceDict

namespace FltWs24
namespace OrderBox

open AlgebraicCurve IsLocalRing

section PlaceOrder

variable {k₀ k Fk : Type*} [Field k₀] [Field k] [Field Fk] [Algebra k Fk]
  [Algebra k₀ k] [Algebra k₀ Fk] [IsScalarTower k₀ k Fk]

theorem ord_add_ge (w : Place k Fk) (x y : Fk) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (w.ord x) (w.ord y) ≤ w.ord (x + y) := by
  have h := w.adicValuation.map_add x y

  have hx' := w.adicValuation_ne_zero hx
  have hy' := w.adicValuation_ne_zero hy
  have hxy' := w.adicValuation_ne_zero hxy
  unfold Place.ord
  rcases le_max_iff.mp h with h1 | h1
  · have := WithZero.log_le_log hxy' hx' |>.mpr h1
    refine le_trans (min_le_left _ _) ?_
    omega
  · have := WithZero.log_le_log hxy' hy' |>.mpr h1
    refine le_trans (min_le_right _ _) ?_
    omega

theorem ord_algebraMap_eq_zero (w : Place k Fk) {c : k} (hc : c ≠ 0) : w.ord (algebraMap k Fk c) = 0 := by
  have hu : IsUnit (⟨algebraMap k Fk c, w.algebraMap_mem' c⟩ : w.toValuationSubring) :=
    ⟨⟨⟨algebraMap k Fk c, w.algebraMap_mem' c⟩, ⟨algebraMap k Fk c⁻¹, w.algebraMap_mem' c⁻¹⟩,
      Subtype.ext (by
        show algebraMap k Fk c * algebraMap k Fk c⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hc, map_one]),
      Subtype.ext (by
        show algebraMap k Fk c⁻¹ * algebraMap k Fk c = 1
        rw [← map_mul, inv_mul_cancel₀ hc, map_one])⟩, rfl⟩
  obtain ⟨u, hu'⟩ := hu
  have := w.ord_coe_unit u
  rw [hu'] at this
  exact this

end PlaceOrder

end FltWs24.OrderBox

namespace FltWs24
namespace OrderBox

open AlgebraicCurve IsLocalRing

section Lift

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem exists_normaliser {ι : Type*} (s : Finset ι) (c : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ s) (hc₀ : c i₀ ≠ 0) :
    ∃ j ∈ s, c j ≠ 0 ∧ ∀ i ∈ s, c i * (c j)⁻¹ ∈ A := by
  classical
  obtain ⟨j, hjs, hmax⟩ := s.exists_max_image (fun i => A.valuation (c i)) ⟨i₀, hi₀⟩
  have hvj : A.valuation (c j) ≠ 0 := by
    intro h0
    have := hmax i₀ hi₀
    rw [h0, le_zero_iff, Valuation.zero_iff] at this
    exact hc₀ this
  have hcj : c j ≠ 0 := fun h => hvj (by rw [h, Valuation.map_zero])
  refine ⟨j, hjs, hcj, fun i hi => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv]
  calc A.valuation (c i) * (A.valuation (c j))⁻¹
      ≤ A.valuation (c j) * (A.valuation (c j))⁻¹ := mul_le_mul_left (hmax i hi) _
    _ = 1 := mul_inv_cancel₀ hvj

theorem linearIndependent_of_residuePair (R₁ R₂ : RegularProlongation A F Fb)
    {ι : Type*} (f : ι → F) (h₁ : ∀ i, f i ∈ R₁.integers) (h₂ : ∀ i, f i ∈ R₂.integers)
    (hli : LinearIndependent (ResidueField A)
      (fun i => (R₁.residue ⟨f i, h₁ i⟩, R₂.residue ⟨f i, h₂ i⟩))) :
    LinearIndependent L f := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum
  by_contra hne
  push_neg at hne
  obtain ⟨i₀, hi₀, hc₀⟩ := hne
  obtain ⟨j, hjs, hcj, hA⟩ := exists_normaliser (A := A) s c hi₀ hc₀

  let a : ι → A := fun i => if hi : i ∈ s then ⟨c i * (c j)⁻¹, hA i hi⟩ else 0
  have ha : ∀ i ∈ s, ((a i : A) : L) = c i * (c j)⁻¹ := fun i hi => by simp [a, hi]
  have haj : a j = 1 := by
    apply Subtype.ext
    rw [ha j hjs]
    simp [mul_inv_cancel₀ hcj]

  have hrel : ∑ i ∈ s, algebraMap L F ((a i : A) : L) * f i = 0 := by
    have : ∑ i ∈ s, algebraMap L F ((a i : A) : L) * f i = (c j)⁻¹ • ∑ i ∈ s, c i • f i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ha i hi, ← Algebra.smul_def, smul_smul, mul_comm]
    rw [this, hsum, smul_zero]
  have key : ∀ (R : RegularProlongation A F Fb) (hR : ∀ i, f i ∈ R.integers),
      ∑ i ∈ s, (IsLocalRing.residue A (a i)) • R.residue ⟨f i, hR i⟩ = 0 := by
    intro R hR
    let x : ι → R.integers := fun i =>
      ⟨algebraMap L F ((a i : A) : L) * f i, mul_mem ((R.algebraMap_mem_iff _).mpr (a i).2) (hR i)⟩
    have hx0 : ∑ i ∈ s, x i = 0 := by
      apply Subtype.ext
      exact (map_sum R.integers.subtype x s).trans hrel
    have := congrArg R.residue hx0
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hxi : x i = ⟨_, (R.algebraMap_mem_iff _).mpr (a i).2⟩ * ⟨f i, hR i⟩ := rfl
    rw [hxi, map_mul, R.residue_algebraMap (a i), Algebra.smul_def]
  have hpair : ∑ i ∈ s, (IsLocalRing.residue A (a i)) •
      (R₁.residue ⟨f i, h₁ i⟩, R₂.residue ⟨f i, h₂ i⟩) = 0 := by
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · rw [Prod.fst_sum, Prod.fst_zero, ← key R₁ h₁]
      exact Finset.sum_congr rfl fun i _ => rfl
    · rw [Prod.snd_sum, Prod.snd_zero, ← key R₂ h₂]
      exact Finset.sum_congr rfl fun i _ => rfl
  have h0 := (linearIndependent_iff'.mp hli) s (fun i => IsLocalRing.residue A (a i)) hpair j hjs
  simp only [haj, map_one] at h0
  exact one_ne_zero h0

theorem finiteDimensional_span_pairSet (R₁ R₂ : RegularProlongation A F Fb)
    (V : Submodule L F) [FiniteDimensional L V] :
    FiniteDimensional (ResidueField A)
      (Submodule.span (ResidueField A)
        {p : Fb × Fb | ∃ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers),
          f ∈ V ∧ p = (R₁.residue ⟨f, hf₁⟩, R₂.residue ⟨f, hf₂⟩)}) := by
  classical
  set S : Set (Fb × Fb) := {p : Fb × Fb | ∃ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers),
          f ∈ V ∧ p = (R₁.residue ⟨f, hf₁⟩, R₂.residue ⟨f, hf₂⟩)} with hS
  obtain ⟨T, hTS, hspan, hli⟩ := exists_linearIndependent (ResidueField A) S
  have hTfin : T.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨T', hT', hcard⟩ := hinf.exists_subset_card_eq (Module.finrank L V + 1)

    have hpre : ∀ p ∈ T', ∃ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers),
        f ∈ V ∧ p = (R₁.residue ⟨f, hf₁⟩, R₂.residue ⟨f, hf₂⟩) := fun p hp =>
      hTS (hT' (Finset.mem_coe.mpr hp))
    choose! g hg₁ hg₂ hgV hgp using hpre

    have hsub : LinearIndependent (ResidueField A) (fun p : T' => ((p : Fb × Fb))) := by
      have := hli.comp (fun p : T' => (⟨(p : Fb × Fb), hT' (Finset.mem_coe.mpr p.2)⟩ : T))
        (fun p p' h => by
          apply Subtype.ext
          have h' := congrArg (fun z : T => (z : Fb × Fb)) h
          simpa using h')
      exact this
    have hfeq : (fun p : T' => (R₁.residue ⟨g p, hg₁ p p.2⟩, R₂.residue ⟨g p, hg₂ p p.2⟩))
        = (fun p : T' => ((p : Fb × Fb))) := by
      funext p
      exact (hgp p p.2).symm
    have hliT' : LinearIndependent (ResidueField A)
        (fun p : T' => (R₁.residue ⟨g p, hg₁ p p.2⟩, R₂.residue ⟨g p, hg₂ p p.2⟩)) := by
      rw [hfeq]; exact hsub

    have hliL : LinearIndependent L (fun p : T' => g p) :=
      linearIndependent_of_residuePair R₁ R₂ _ (fun p => hg₁ p p.2) (fun p => hg₂ p p.2) hliT'
    have hliV : LinearIndependent L (fun p : T' => (⟨g p, hgV p p.2⟩ : V)) :=
      LinearIndependent.of_comp V.subtype hliL
    have hle := hliV.fintype_card_le_finrank
    rw [Fintype.card_coe, hcard] at hle
    omega
  rw [← hspan]
  exact FiniteDimensional.span_of_finite (ResidueField A) hTfin

end Lift

end FltWs24.OrderBox

namespace FltWs24
namespace Perturb

open AlgebraicCurve IsLocalRing

section Upstairs

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]

theorem algebraMap_mem_riemannRochSpace {E : Divisor L F} (hE : ∀ W, 0 ≤ E W) (c : L) :
    algebraMap L F c ∈ riemannRochSpace E := by
  rw [mem_riemannRochSpace_iff]
  intro W
  by_cases hc : c = 0
  · left; rw [hc, map_zero]
  · right
    rw [FltWs24.OrderBox.ord_algebraMap_eq_zero W hc]
    have := hE W
    omega

theorem algebraMap_mem_integers (R : RegularProlongation A F Fb) (a : A) :
    algebraMap L F (a : L) ∈ R.integers :=
  (R.algebraMap_mem_iff _).mpr a.2

theorem residue_add_algebraMap (R : RegularProlongation A F Fb) {f : F} (hf : f ∈ R.integers) (a : A) :
    R.residue ⟨f + algebraMap L F (a : L), add_mem hf (algebraMap_mem_integers R a)⟩
      = R.residue ⟨f, hf⟩ + algebraMap (ResidueField A) Fb (IsLocalRing.residue A a) := by
  have : (⟨f + algebraMap L F (a : L), add_mem hf (algebraMap_mem_integers R a)⟩ : R.integers)
      = ⟨f, hf⟩ + ⟨_, algebraMap_mem_integers R a⟩ := rfl
  rw [this, map_add, R.residue_algebraMap a]

theorem exists_add_algebraMap_residue_ne_zero [Infinite (ResidueField A)]
    (R₁ R₂ : RegularProlongation A F Fb) {f : F} (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) :
    ∃ a : A, R₁.residue ⟨f + algebraMap L F (a : L), add_mem h₁ (algebraMap_mem_integers R₁ a)⟩ ≠ 0 ∧
             R₂.residue ⟨f + algebraMap L F (a : L), add_mem h₂ (algebraMap_mem_integers R₂ a)⟩ ≠ 0 := by
  classical
  set r₁ := R₁.residue ⟨f, h₁⟩
  set r₂ := R₂.residue ⟨f, h₂⟩

  obtain ⟨x, hx⟩ : ∃ x : ResidueField A, x ∉ ({y | algebraMap _ Fb y = -r₁} ∪ {y | algebraMap _ Fb y = -r₂}) := by
    have hfin : Set.Finite ({y : ResidueField A | algebraMap _ Fb y = -r₁} ∪ {y | algebraMap _ Fb y = -r₂}) := by
      refine Set.Finite.union ?_ ?_ <;>
      · refine Set.Subsingleton.finite ?_
        intro y hy y' hy'
        exact (algebraMap (ResidueField A) Fb).injective (hy.trans hy'.symm)
    exact hfin.infinite_compl.nonempty
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨a, ?_, ?_⟩
  · rw [residue_add_algebraMap R₁ h₁ a]
    intro h
    exact hx (Or.inl (eq_neg_of_add_eq_zero_right h))
  · rw [residue_add_algebraMap R₂ h₂ a]
    intro h
    exact hx (Or.inr (eq_neg_of_add_eq_zero_right h))

theorem exists_add_algebraMap_residue_ne_zero_notMem [Infinite (ResidueField A)]
    (R₁ R₂ : RegularProlongation A F Fb) {f : F} (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers)
    (S : Set (ResidueField A)) (hS : S.Finite) :
    ∃ a : A, IsLocalRing.residue A a ∉ S ∧
      R₁.residue ⟨f + algebraMap L F (a : L), add_mem h₁ (algebraMap_mem_integers R₁ a)⟩ ≠ 0 ∧
      R₂.residue ⟨f + algebraMap L F (a : L), add_mem h₂ (algebraMap_mem_integers R₂ a)⟩ ≠ 0 := by
  classical
  set r₁ := R₁.residue ⟨f, h₁⟩
  set r₂ := R₂.residue ⟨f, h₂⟩
  obtain ⟨x, hx⟩ : ∃ x : ResidueField A,
      x ∉ (S ∪ ({y | algebraMap _ Fb y = -r₁} ∪ {y | algebraMap _ Fb y = -r₂})) := by
    have hfin : Set.Finite (S ∪ ({y : ResidueField A | algebraMap _ Fb y = -r₁} ∪ {y | algebraMap _ Fb y = -r₂})) := by
      refine hS.union (Set.Finite.union ?_ ?_) <;>
      · refine Set.Subsingleton.finite ?_
        intro y hy y' hy'
        exact (algebraMap (ResidueField A) Fb).injective (hy.trans hy'.symm)
    exact hfin.infinite_compl.nonempty
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  refine ⟨a, fun h => hx (Or.inl h), ?_, ?_⟩
  · rw [residue_add_algebraMap R₁ h₁ a]
    intro h
    exact hx (Or.inr (Or.inl (eq_neg_of_add_eq_zero_right h)))
  · rw [residue_add_algebraMap R₂ h₂ a]
    intro h
    exact hx (Or.inr (Or.inr (eq_neg_of_add_eq_zero_right h)))

end Upstairs

section Downstairs

variable {k Fk : Type*} [Field k] [Field Fk] [Algebra k Fk]

theorem ord_add_algebraMap_of_ord_neg (w : Place k Fk) {g : Fk} (hg : w.ord g < 0) (c : k) :
    w.ord (g + algebraMap k Fk c) = w.ord g := by
  have hg0 : g ≠ 0 := by rintro rfl; rw [Place.ord_zero] at hg; exact lt_irrefl _ hg
  by_cases hc : c = 0
  · rw [hc, map_zero, add_zero]
  have hc0 : algebraMap k Fk c ≠ 0 := (map_ne_zero _).mpr hc
  have hordc := FltWs24.OrderBox.ord_algebraMap_eq_zero w hc
  have hsum0 : g + algebraMap k Fk c ≠ 0 := by
    intro h
    have : g = -algebraMap k Fk c := eq_neg_of_add_eq_zero_left h
    rw [this, show -algebraMap k Fk c = algebraMap k Fk (-c) by rw [map_neg],
      FltWs24.OrderBox.ord_algebraMap_eq_zero w (neg_ne_zero.mpr hc)] at hg
    exact lt_irrefl _ hg
  apply le_antisymm
  ·
    by_contra hlt
    push_neg at hlt
    have h2 := FltWs24.OrderBox.ord_add_ge w (g + algebraMap k Fk c) (algebraMap k Fk (-c)) hsum0
      ((map_ne_zero _).mpr (neg_ne_zero.mpr hc)) (by rw [map_neg, add_neg_cancel_right]; exact hg0)
    rw [map_neg, add_neg_cancel_right, ← map_neg,
      FltWs24.OrderBox.ord_algebraMap_eq_zero w (neg_ne_zero.mpr hc)] at h2

    have : min (w.ord (g + algebraMap k Fk c)) 0 ≤ w.ord g := h2
    rw [min_le_iff] at this
    rcases this with h | h <;> omega
  · have h1 := FltWs24.OrderBox.ord_add_ge w g (algebraMap k Fk c) hg0 hc0 hsum0
    rw [hordc, min_eq_left (le_of_lt hg)] at h1
    exact h1

theorem ord_add_algebraMap_ge_of_ge (w : Place k Fk) {g : Fk} {n : ℤ} (hn : n ≤ 0)
    (hg : g = 0 ∨ n ≤ w.ord g) (c : k) :
    g + algebraMap k Fk c = 0 ∨ n ≤ w.ord (g + algebraMap k Fk c) := by
  by_cases h0 : g + algebraMap k Fk c = 0
  · exact Or.inl h0
  right
  by_cases hneg : w.ord (g + algebraMap k Fk c) < 0
  ·
    have := ord_add_algebraMap_of_ord_neg w hneg (-c)
    rw [map_neg, add_neg_cancel_right] at this

    rcases hg with rfl | hg
    · rw [zero_add, FltWs24.OrderBox.ord_algebraMap_eq_zero w (by
        intro hc; apply h0; rw [hc, map_zero, add_zero])]  at hneg
      exact absurd hneg (lt_irrefl 0)
    · rw [this] at hg; exact hg
  · push_neg at hneg; exact hn.trans hneg

end Downstairs

end FltWs24.Perturb

namespace FltWs24
namespace DivTools

open AlgebraicCurve

section Finsupp

variable {α β : Type*}

theorem mapDomain_le_mapDomain (f : α → β) {D E : α →₀ ℤ} (h : D ≤ E) :
    Finsupp.mapDomain f D ≤ Finsupp.mapDomain f E :=
  Finsupp.mapDomain_mono h

theorem mapDomain_neg (f : α → β) (E : α →₀ ℤ) :
    Finsupp.mapDomain f (-E) = -Finsupp.mapDomain f E :=
  map_neg (Finsupp.mapDomain.addMonoidHom f) E

theorem neg_mapDomain_apply_le (f : α → β) {D E : α →₀ ℤ} (h : -E ≤ D) (v : β) :
    -(Finsupp.mapDomain f E v) ≤ Finsupp.mapDomain f D v := by
  have := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := f) h) v
  rwa [mapDomain_neg, Finsupp.coe_neg, Pi.neg_apply] at this

theorem filter_le_filter (p : α → Prop) [DecidablePred p] {D E : α →₀ ℤ} (h : D ≤ E) :
    D.filter p ≤ E.filter p := by
  intro a
  rw [Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · exact h a
  · exact le_rfl

theorem filter_neg (p : α → Prop) [DecidablePred p] (E : α →₀ ℤ) :
    (-E).filter p = -E.filter p := by
  ext a
  simp only [Finsupp.filter_apply, Finsupp.coe_neg, Pi.neg_apply]
  split_ifs <;> simp

theorem neg_mapDomain_filter_apply_le (f : α → β) (p : α → Prop) [DecidablePred p]
    {D E : α →₀ ℤ} (h : -E ≤ D) (v : β) :
    -(Finsupp.mapDomain f (E.filter p) v) ≤ Finsupp.mapDomain f (D.filter p) v := by
  apply neg_mapDomain_apply_le
  rw [← filter_neg]
  exact filter_le_filter p h

end Finsupp

section RR

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem neg_le_of_mem_riemannRochSpace {E D : Divisor K F} {f : F} (hf : f ∈ riemannRochSpace E) (hf0 : f ≠ 0)
    (hD : ∀ W, D W = W.ord f) : -E ≤ D := by
  intro W
  rw [Finsupp.coe_neg, Pi.neg_apply, hD W]
  exact ((mem_riemannRochSpace_iff.mp hf) W).resolve_left hf0

end RR

end FltWs24.DivTools

namespace FltWs24
namespace DivTools
open AlgebraicCurve ModularCurve

theorem exists_principalDivisor {N : ℕ} [NeZero N] (f : ↥(modularFunctionFieldBar N)) (hf : f ≠ 0) :
    ∃ D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), ∀ W, D W = W.ord f := by
  have hPD := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hPD) f hf
  exact ⟨D, hD⟩

end FltWs24.DivTools

namespace FltWs24
namespace Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Generic

variable {α β : Type*}

theorem sum_single_apply [DecidableEq α] (S : Finset α) (g : α → ℤ) (x : α) :
    (∑ y ∈ S, Finsupp.single y (g y)) x = if x ∈ S then g x else 0 := by
  rw [Finsupp.finset_sum_apply]
  simp_rw [Finsupp.single_apply]
  exact Finset.sum_ite_eq' S x g

theorem sum_single_comp_apply [DecidableEq α] [DecidableEq β] (S : Finset α) (ψ : α → β) (g : α → ℤ)
    (hψ : ∀ y ∈ S, ∀ y' ∈ S, ψ y = ψ y' → y = y') {a : α} (ha : a ∈ S) :
    (∑ y ∈ S, Finsupp.single (ψ y) (g y)) (ψ a) = g a := by
  rw [Finsupp.finset_sum_apply]
  simp_rw [Finsupp.single_apply]
  rw [Finset.sum_eq_single a]
  · rw [if_pos rfl]
  · intro y hy hya
    rw [if_neg]
    intro h
    exact hya (hψ y hy a ha h)
  · intro h; exact absurd ha h

theorem sum_single_comp_apply_of_forall_ne [DecidableEq β] (S : Finset α) (ψ : α → β) (g : α → ℤ)
    {x : β} (hx : ∀ y ∈ S, ψ y ≠ x) :
    (∑ y ∈ S, Finsupp.single (ψ y) (g y)) x = 0 := by
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Finsupp.single_apply, if_neg (hx y hy)]

theorem mapDomain_apply_eq_sum_filter [DecidableEq β] (f : α → β) (D : α →₀ ℤ) (v : β) :
    Finsupp.mapDomain f D v = ∑ W ∈ D.support.filter (fun W => f W = v), D W := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finset_sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finsupp.single_apply]

theorem mapDomain_apply_eq_zero_of_forall [DecidableEq β] (f : α → β) (D : α →₀ ℤ) (v : β)
    (h : ∀ W ∈ D.support, f W ≠ v) : Finsupp.mapDomain f D v = 0 := by
  rw [mapDomain_apply_eq_sum_filter]
  refine Finset.sum_eq_zero fun W hW => ?_
  rw [Finset.mem_filter] at hW
  exact absurd hW.2 (h W hW.1)

theorem mapDomain_nonneg_apply (f : α → β) {D : α →₀ ℤ} (hD : ∀ a, 0 ≤ D a) (v : β) :
    0 ≤ Finsupp.mapDomain f D v := by
  classical
  rw [mapDomain_apply_eq_sum_filter]
  exact Finset.sum_nonneg fun W _ => hD W

theorem sum_mapDomain_id (f : α → β) (D : α →₀ ℤ) :
    (Finsupp.mapDomain f D).sum (fun _ n => n) = D.sum (fun _ n => n) :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem filter_eq_zero_of_nonneg (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a) (p : α → Prop) [DecidablePred p]
    (hp : ∀ a, p a ↔ D a < 0) : D.filter p = 0 := by
  rw [Finsupp.filter_eq_zero_iff]
  intro a ha
  have := hD a
  have h2 := (hp a).mp ha
  omega

theorem filter_eq_self_of_nonneg (D : α →₀ ℤ) (hD : ∀ a, 0 ≤ D a) (p : α → Prop) [DecidablePred p]
    (hp : ∀ a, p a ↔ 0 < D a) : D.filter p = D := by
  rw [Finsupp.filter_eq_self_iff]
  intro a ha
  rw [hp]
  have := hD a
  omega

end Generic

section Degree

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = D.sum (fun _ n => n) := by
  show Finsupp.liftAddHom (fun v => AddMonoidHom.mulRight ((v.deg : ℕ) : ℤ)) D = _
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v _ => ?_
  rw [AddMonoidHom.mulRight_apply, h v, Nat.cast_one, mul_one]

theorem degree_eq_sum_support_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [degree_eq_sum_of_deg_eq_one h]; rfl

theorem degree_single_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) (v : Place K F) (n : ℤ) :
    Divisor.degree (Finsupp.single v n) = n := by
  rw [Divisor.degree_single, h v, Nat.cast_one, mul_one]

theorem degree_sum_single_of_deg_eq_one (h : ∀ v : Place K F, v.deg = 1) {ι : Type*} (S : Finset ι)
    (ψ : ι → Place K F) (g : ι → ℤ) :
    Divisor.degree (∑ i ∈ S, Finsupp.single (ψ i) (g i)) = ∑ i ∈ S, g i := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => degree_single_of_deg_eq_one h _ _

theorem degree_filter_eq_sum (h : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) (p : Place K F → Prop)
    [DecidablePred p] : Divisor.degree (D.filter p) = ∑ v ∈ D.support.filter p, D v := by
  rw [degree_eq_sum_support_of_deg_eq_one h, Finsupp.support_filter]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.mem_filter] at hv
  rw [Finsupp.filter_apply, if_pos hv.2]

end Degree

end FltWs24.Asm

namespace FltWs24
namespace Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section Site

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

local notation "Qb" => AlgebraicClosure ℚ
local notation "Fq" => modularFunctionFieldBar (1 * q)
local notation "Ck" => modularFunctionFieldC k 1
local notation "Plk" => Place k (modularFunctionFieldC k 1)
local notation "PlF" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_np1 (a : k) : φ (frobNodePair q a).1 = (frobNodePair q a).2 := by
  rw [frobNodePair_fst, frobNodePair_snd]
  exact ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr a

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_np2 (a : k) (ha2 : a ^ (q ^ 2) = a) : φ (frobNodePair q a).2 = (frobNodePair q a).1 := by
  have h : (a ^ q) ^ q = a := by rw [← pow_mul, ← pow_two, ha2]
  rw [frobNodePair_fst, frobNodePair_snd, ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr, h]

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_frob_np1 (a : k) (ha2 : a ^ (q ^ 2) = a) : φ (φ (frobNodePair q a).1) = (frobNodePair q a).1 := by
  rw [frob_np1, frob_np2 a ha2]

omit [IsAlgClosed k] [DecidableEq k] in
theorem np1_injective : Function.Injective (fun a : k => (frobNodePair q a).1) := fun a b h =>
  charLGeomPlaceOfPoint_injective k (by simpa only [frobNodePair_fst] using h)

omit [IsAlgClosed k] [DecidableEq k] in
theorem np2_injective : Function.Injective (fun a : k => (frobNodePair q a).2) := fun a b h => by
  have h' : charLGeomPlaceOfPoint k (a ^ q) = charLGeomPlaceOfPoint k (b ^ q) := by
    simpa only [frobNodePair_snd] using h
  exact frobenius_inj k q (charLGeomPlaceOfPoint_injective k h')

omit [IsAlgClosed k] [DecidableEq k] in

theorem frob_injOn_fixed {v w : Plk} (hv : φ (φ v) = v) (hw : φ (φ w) = w) (h : φ v = φ w) : v = w := by
  rw [← hv, ← hw, h]

omit [IsAlgClosed k] [DecidableEq k] in
theorem frob_fixed_of_fixed {v : Plk} (hv : φ (φ v) = v) : φ (φ (φ v)) = φ v := by rw [hv]

theorem mapDomain_redFst_fstPart_eq_zero (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (E : Divisor Qb Fq) (v : Plk) (hv : φ (φ v) = v) :
    Finsupp.mapDomain P.redFst (P.fstPart E) v = 0 := by
  classical
  apply mapDomain_apply_eq_zero_of_forall
  intro W hW h
  have hW' : P.IsStrictTypeOne W := by
    unfold PlaceSpecialization.fstPart at hW
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    exact hW.2
  exact hW'.2 (h ▸ hv)

theorem mapDomain_redSnd_sndPart_eq_zero (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (E : Divisor Qb Fq) (v : Plk) (hv : φ (φ v) = v) :
    Finsupp.mapDomain P.redSnd (P.sndPart E) v = 0 := by
  classical
  apply mapDomain_apply_eq_zero_of_forall
  intro W hW h
  have hW' : P.IsStrictTypeTwo W := by
    unfold PlaceSpecialization.sndPart at hW
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    exact hW.2
  exact hW'.2 (h ▸ hv)

variable (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

open Classical in

noncomputable def D1 (E : Divisor Qb Fq) (Vfix : Finset Plk) (s : Plk → ℤ) (Sm : Finset k) (n₁ : k → ℕ) :
    Divisor k Ck :=
  Finsupp.mapDomain P.redFst (P.fstPart E)
    + (∑ v ∈ Vfix, Finsupp.single v (-s v))
    + (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).1 (n₁ a : ℤ))
    + Finsupp.single (P.redFst (cuspInftyBar (1 * q)))
        (Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))))

open Classical in

noncomputable def D2 (E : Divisor Qb Fq) (Vfix : Finset Plk) (s : Plk → ℤ) (Sm : Finset k) (n₂ : k → ℕ) :
    Divisor k Ck :=
  Finsupp.mapDomain P.redSnd (P.sndPart E)
    + (∑ v ∈ Vfix, Finsupp.single (φ v) (Finsupp.mapDomain P.redFst E v + s v))
    + (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).2 (n₂ a : ℤ))
    + Finsupp.single (P.redSnd (cuspZeroBar (1 * q)))
        (Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))))

structure IndexHyp (Vfix : Finset Plk) (Sm : Finset k) : Prop where
  fixV : ∀ v ∈ Vfix, φ (φ v) = v
  neV : ∀ v ∈ Vfix, v ≠ P.redFst (cuspInftyBar (1 * q))
  notNode : ∀ v ∈ Vfix, ∀ a ∈ Sm, v ≠ (frobNodePair q a).1
  sq : ∀ a ∈ Sm, a ^ (q ^ 2) = a

variable {P}

section Eval

open Classical in
theorem D1_apply {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₁ : k → ℕ} (v : Plk) : D1 P E Vfix s Sm n₁ v =
    Finsupp.mapDomain P.redFst (P.fstPart E) v
      + (∑ v' ∈ Vfix, Finsupp.single v' (-s v')) v
      + (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).1 (n₁ a : ℤ)) v
      + (Finsupp.single (P.redFst (cuspInftyBar (1 * q)))
          (Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))))) v := by
  simp only [D1, Finsupp.coe_add, Pi.add_apply]

open Classical in
theorem D2_apply {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₂ : k → ℕ} (w : Plk) : D2 P E Vfix s Sm n₂ w =
    Finsupp.mapDomain P.redSnd (P.sndPart E) w
      + (∑ v ∈ Vfix, Finsupp.single (φ v) (Finsupp.mapDomain P.redFst E v + s v)) w
      + (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).2 (n₂ a : ℤ)) w
      + (Finsupp.single (P.redSnd (cuspZeroBar (1 * q)))
          (Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))))) w := by
  simp only [D2, Finsupp.coe_add, Pi.add_apply]

open Classical in
theorem D1_sum2 {Vfix : Finset Plk} {s : Plk → ℤ} (v : Plk) : (∑ v' ∈ Vfix, Finsupp.single v' (-s v')) v = if v ∈ Vfix then -s v else 0 := by
  classical
  exact sum_single_apply Vfix (fun v' => -s v') v

theorem D1_sum3_node {Sm : Finset k} {n₁ : k → ℕ} {a : k} (ha : a ∈ Sm) :
    (∑ a' ∈ Sm, Finsupp.single (frobNodePair q a').1 (n₁ a' : ℤ)) (frobNodePair q a).1 = n₁ a := by
  classical
  exact sum_single_comp_apply Sm (fun a' => (frobNodePair q a').1) (fun a' => (n₁ a' : ℤ))
    (fun y _ y' _ h => np1_injective h) ha

theorem D1_sum3_zero {Sm : Finset k} {n₁ : k → ℕ} {v : Plk} (hv : ∀ a ∈ Sm, v ≠ (frobNodePair q a).1) :
    (∑ a' ∈ Sm, Finsupp.single (frobNodePair q a').1 (n₁ a' : ℤ)) v = 0 := by
  classical
  exact sum_single_comp_apply_of_forall_ne Sm (fun a' => (frobNodePair q a').1) (fun a' => (n₁ a' : ℤ))
    (fun a ha h => hv a ha h.symm)

theorem node_ne_of_not_fixed {Sm : Finset k} {Vfix : Finset Plk} (H : IndexHyp P Vfix Sm) {v : Plk} (hv : φ (φ v) ≠ v) : ∀ a ∈ Sm, v ≠ (frobNodePair q a).1 :=
  fun a ha h => hv (by rw [h]; exact frob_frob_np1 a (H.sq a ha))

theorem cusp_fixed (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : φ (φ (P.redFst (cuspInftyBar (1 * q)))) = P.redFst (cuspInftyBar (1 * q)) := by
  rw [FltWs24.PlaceDict.frob_redFst_cuspInftyBar P, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]

open Classical in
theorem D1_sum4 {E : Divisor Qb Fq} (v : Plk) (hv : v ≠ P.redFst (cuspInftyBar (1 * q))) :
    (Finsupp.single (P.redFst (cuspInftyBar (1 * q)))
      (Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))))) v = 0 := by
  rw [Finsupp.single_apply, if_neg (fun h => hv h.symm)]

theorem D1_of_not_fixed {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₁ : k → ℕ} (H : IndexHyp P Vfix Sm) (v : Plk) (hv : φ (φ v) ≠ v) :
    D1 P E Vfix s Sm n₁ v = Finsupp.mapDomain P.redFst (P.fstPart E) v := by
  classical
  have hvV : v ∉ Vfix := fun h => hv (H.fixV v h)
  have hvc : v ≠ P.redFst (cuspInftyBar (1 * q)) := fun h => hv (by rw [h]; exact cusp_fixed P)
  rw [D1_apply, D1_sum2, if_neg hvV, D1_sum3_zero (node_ne_of_not_fixed H hv), D1_sum4 v hvc]
  ring

theorem D1_of_mem_Vfix {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₁ : k → ℕ} (H : IndexHyp P Vfix Sm) (v : Plk) (hv : v ∈ Vfix) : D1 P E Vfix s Sm n₁ v = -s v := by
  classical
  rw [D1_apply, D1_sum2, if_pos hv, mapDomain_redFst_fstPart_eq_zero P E v (H.fixV v hv),
    D1_sum3_zero (H.notNode v hv), D1_sum4 v (H.neV v hv)]
  ring

theorem D1_node {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₁ : k → ℕ} (H : IndexHyp P Vfix Sm) {a : k} (ha : a ∈ Sm) : D1 P E Vfix s Sm n₁ (frobNodePair q a).1 = n₁ a := by
  classical
  rw [D1_apply, D1_sum2, if_neg (fun h => H.notNode _ h a ha rfl),
    mapDomain_redFst_fstPart_eq_zero P E _ (frob_frob_np1 a (H.sq a ha)), D1_sum3_node ha,
    D1_sum4 _ (FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a)]
  ring

open Classical in

theorem D1_cusp {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₁ : k → ℕ} (H : IndexHyp P Vfix Sm) : D1 P E Vfix s Sm n₁ (P.redFst (cuspInftyBar (1 * q)))
    = Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) := by
  classical
  rw [D1_apply, D1_sum2, if_neg (fun h => H.neV _ h rfl), mapDomain_redFst_fstPart_eq_zero P E _ (cusp_fixed P),
    D1_sum3_zero (fun a ha h => FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a h.symm),
    Finsupp.single_apply, if_pos rfl]
  ring

theorem D1_of_fixed_else {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₁ : k → ℕ} (H : IndexHyp P Vfix Sm) (v : Plk) (hv : φ (φ v) = v) (hvc : v ≠ P.redFst (cuspInftyBar (1 * q)))
    (hvn : ∀ a ∈ Sm, v ≠ (frobNodePair q a).1) (hvV : v ∉ Vfix) : D1 P E Vfix s Sm n₁ v = 0 := by
  classical
  rw [D1_apply, D1_sum2, if_neg hvV, mapDomain_redFst_fstPart_eq_zero P E v hv, D1_sum3_zero hvn,
    D1_sum4 v hvc]
  ring

open Classical in
theorem D2_sum2_frob {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} (H : IndexHyp P Vfix Sm) {v : Plk} (hvf : φ (φ v) = v) :
    (∑ v' ∈ Vfix, Finsupp.single (φ v') (Finsupp.mapDomain P.redFst E v' + s v')) (φ v)
      = if v ∈ Vfix then Finsupp.mapDomain P.redFst E v + s v else 0 := by
  classical
  split_ifs with hv
  · exact sum_single_comp_apply Vfix (fun v' => φ v') (fun v' => Finsupp.mapDomain P.redFst E v' + s v')
      (fun y hy y' hy' h => frob_injOn_fixed (H.fixV y hy) (H.fixV y' hy') h) hv
  · exact sum_single_comp_apply_of_forall_ne Vfix (fun v' => φ v')
      (fun v' => Finsupp.mapDomain P.redFst E v' + s v')
      (fun y hy h => hv ((frob_injOn_fixed (H.fixV y hy) hvf h) ▸ hy))

theorem D2_sum2_zero {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {w : Plk} (hw : ∀ v ∈ Vfix, φ v ≠ w) :
    (∑ v' ∈ Vfix, Finsupp.single (φ v') (Finsupp.mapDomain P.redFst E v' + s v')) w = 0 := by
  classical
  exact sum_single_comp_apply_of_forall_ne Vfix (fun v' => φ v')
      (fun v' => Finsupp.mapDomain P.redFst E v' + s v') hw

theorem D2_sum3_node {Sm : Finset k} {n₂ : k → ℕ} {a : k} (ha : a ∈ Sm) :
    (∑ a' ∈ Sm, Finsupp.single (frobNodePair q a').2 (n₂ a' : ℤ)) (frobNodePair q a).2 = n₂ a := by
  classical
  exact sum_single_comp_apply Sm (fun a' => (frobNodePair q a').2) (fun a' => (n₂ a' : ℤ))
    (fun y _ y' _ h => np2_injective h) ha

theorem D2_sum3_zero {Sm : Finset k} {n₂ : k → ℕ} {w : Plk} (hw : ∀ a ∈ Sm, w ≠ (frobNodePair q a).2) :
    (∑ a' ∈ Sm, Finsupp.single (frobNodePair q a').2 (n₂ a' : ℤ)) w = 0 := by
  classical
  exact sum_single_comp_apply_of_forall_ne Sm (fun a' => (frobNodePair q a').2) (fun a' => (n₂ a' : ℤ))
    (fun a ha h => hw a ha h.symm)

theorem cusp0_eq (P : PlaceSpecialization A q 1 data hKr k red hα hβ) : P.redSnd (cuspZeroBar (1 * q)) = P.redFst (cuspInftyBar (1 * q)) :=
  FltWs24.PlaceDict.redSnd_cuspZeroBar_eq P

open Classical in
theorem D2_sum4 {E : Divisor Qb Fq} (w : Plk) (hw : w ≠ P.redFst (cuspInftyBar (1 * q))) :
    (Finsupp.single (P.redSnd (cuspZeroBar (1 * q)))
      (Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))))) w = 0 := by
  rw [Finsupp.single_apply, if_neg (fun h => hw (by rw [← h]; exact cusp0_eq P))]

theorem eq_np1_of_frob_eq {Sm : Finset k} {Vfix : Finset Plk} (H : IndexHyp P Vfix Sm) {v : Plk} (hv : φ (φ v) = v) {a : k} (ha : a ∈ Sm) (h : φ v = (frobNodePair q a).2) :
    v = (frobNodePair q a).1 :=
  frob_injOn_fixed hv (frob_frob_np1 a (H.sq a ha)) (by rw [h, frob_np1])

theorem D2_of_not_fixed {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₂ : k → ℕ} (H : IndexHyp P Vfix Sm) (w : Plk) (hw : φ (φ w) ≠ w) :
    D2 P E Vfix s Sm n₂ w = Finsupp.mapDomain P.redSnd (P.sndPart E) w := by
  classical
  have h2 : ∀ v ∈ Vfix, φ v ≠ w := fun v hv h => hw (by rw [← h]; exact frob_fixed_of_fixed (H.fixV v hv))
  have h3 : ∀ a ∈ Sm, w ≠ (frobNodePair q a).2 := fun a ha h => hw (by
    rw [h, frob_np2 a (H.sq a ha), frob_np1])
  have h4 : w ≠ P.redFst (cuspInftyBar (1 * q)) := fun h => hw (by rw [h]; exact cusp_fixed P)
  rw [D2_apply, D2_sum2_zero h2, D2_sum3_zero h3, D2_sum4 w h4]
  ring

theorem D2_of_mem_Vfix {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₂ : k → ℕ} (H : IndexHyp P Vfix Sm) (v : Plk) (hv : v ∈ Vfix) :
    D2 P E Vfix s Sm n₂ (φ v) = Finsupp.mapDomain P.redFst E v + s v := by
  classical
  have hvf := H.fixV v hv
  have h3 : ∀ a ∈ Sm, φ v ≠ (frobNodePair q a).2 := fun a ha h =>
    H.notNode v hv a ha (eq_np1_of_frob_eq H hvf ha h)
  have h4 : φ v ≠ P.redFst (cuspInftyBar (1 * q)) := fun h => H.neV v hv
    (frob_injOn_fixed hvf (cusp_fixed P) (by rw [h, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]))
  rw [D2_apply, mapDomain_redSnd_sndPart_eq_zero P E _ (frob_fixed_of_fixed hvf), D2_sum2_frob H hvf, if_pos hv,
    D2_sum3_zero h3, D2_sum4 _ h4]
  ring

theorem D2_node {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₂ : k → ℕ} (H : IndexHyp P Vfix Sm) {a : k} (ha : a ∈ Sm) : D2 P E Vfix s Sm n₂ (frobNodePair q a).2 = n₂ a := by
  classical
  have hfx := frob_frob_np1 (data := data) (hKr := hKr) a (H.sq a ha)
  have hfx2 : φ (φ (frobNodePair q a).2) = (frobNodePair q a).2 := by rw [← frob_np1, hfx]
  have h2 : ∀ v ∈ Vfix, φ v ≠ (frobNodePair q a).2 := fun v hv h =>
    H.notNode v hv a ha (eq_np1_of_frob_eq H (H.fixV v hv) ha h)
  have h4 : (frobNodePair q a).2 ≠ P.redFst (cuspInftyBar (1 * q)) := fun h =>
    FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a
      (frob_injOn_fixed hfx (cusp_fixed P) (by rw [frob_np1, h, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]))
  rw [D2_apply, mapDomain_redSnd_sndPart_eq_zero P E _ hfx2, D2_sum2_zero h2, D2_sum3_node ha,
    D2_sum4 _ h4]
  ring

open Classical in
theorem D2_cusp {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₂ : k → ℕ} (H : IndexHyp P Vfix Sm) : D2 P E Vfix s Sm n₂ (P.redSnd (cuspZeroBar (1 * q)))
    = Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) := by
  classical
  have hc : φ (φ (P.redSnd (cuspZeroBar (1 * q)))) = P.redSnd (cuspZeroBar (1 * q)) := by
    rw [cusp0_eq P]; exact cusp_fixed P
  have h2 : ∀ v ∈ Vfix, φ v ≠ P.redSnd (cuspZeroBar (1 * q)) := fun v hv h => H.neV v hv
    (frob_injOn_fixed (H.fixV v hv) (cusp_fixed P)
      (by rw [h, cusp0_eq P, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]))
  have h3 : ∀ a ∈ Sm, P.redSnd (cuspZeroBar (1 * q)) ≠ (frobNodePair q a).2 := fun a ha h =>
    FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a
      (frob_injOn_fixed (frob_frob_np1 a (H.sq a ha)) (cusp_fixed P)
        (by rw [frob_np1, ← h, cusp0_eq P, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]))
  rw [D2_apply, mapDomain_redSnd_sndPart_eq_zero P E _ hc, D2_sum2_zero h2, D2_sum3_zero h3,
    Finsupp.single_apply, if_pos rfl]
  ring

theorem D2_of_fixed_else {E : Divisor Qb Fq} {Vfix : Finset Plk} {s : Plk → ℤ} {Sm : Finset k} {n₂ : k → ℕ} (H : IndexHyp P Vfix Sm) (v : Plk) (hv : φ (φ v) = v) (hvc : v ≠ P.redFst (cuspInftyBar (1 * q)))
    (hvn : ∀ a ∈ Sm, v ≠ (frobNodePair q a).1) (hvV : v ∉ Vfix) : D2 P E Vfix s Sm n₂ (φ v) = 0 := by
  classical
  have h3 : ∀ a ∈ Sm, φ v ≠ (frobNodePair q a).2 := fun a ha h => hvn a ha (eq_np1_of_frob_eq H hv ha h)
  have h4 : φ v ≠ P.redFst (cuspInftyBar (1 * q)) := fun h => hvc
    (frob_injOn_fixed hv (cusp_fixed P) (by rw [h, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]))
  rw [D2_apply, mapDomain_redSnd_sndPart_eq_zero P E _ (frob_fixed_of_fixed hv), D2_sum2_frob H hv, if_neg hvV,
    D2_sum3_zero h3, D2_sum4 _ h4]
  ring

end Eval

end Site

end FltWs24.Asm

namespace FltWs24
namespace Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section SiteC

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)

local notation "Qb" => AlgebraicClosure ℚ
local notation "Fq" => modularFunctionFieldBar (1 * q)
local notation "Ck" => modularFunctionFieldC k 1
local notation "Plk" => Place k (modularFunctionFieldC k 1)
local notation "PlF" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

omit [IsAlgClosed k] [DecidableEq k] in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem ι_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) (modularFunctionFieldFullC (ResidueField A) 1) c)
      = algebraMap k Ck (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  change coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c)
    = algebraMap k (LaurentSeries k) (R.redBar c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 1600000 in
theorem residue₁_coe_eq_zero {f : Fq} (h₁ : f ∈ R.R₁.integers) (h : R.R₁.residue ⟨f, h₁⟩ = 0) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) = 0 := by
  rw [LevelOneProlongationPair.residue₁_apply, h, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 1600000 in
theorem residue₂_coe_eq_zero {f : Fq} (h₂ : f ∈ R.R₂.integers) (h : R.R₂.residue ⟨f, h₂⟩ = 0) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) = 0 := by
  rw [LevelOneProlongationPair.residue₂_apply, h, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 1600000 in
theorem ne_zero_of_residue₁_ne_zero {f : Fq} (h₁ : f ∈ R.R₁.integers) (h : R.R₁.residue ⟨f, h₁⟩ ≠ 0) : f ≠ 0 := by
  intro h0
  apply h
  have : (⟨f, h₁⟩ : R.R₁.integers) = 0 := by
    apply Subtype.ext
    exact h0
  rw [this, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 1600000 in
theorem ne_zero_of_residue₂_ne_zero {f : Fq} (h₂ : f ∈ R.R₂.integers) (h : R.R₂.residue ⟨f, h₂⟩ ≠ 0) : f ≠ 0 := by
  intro h0
  apply h
  have : (⟨f, h₂⟩ : R.R₂.integers) = 0 := by
    apply Subtype.ext
    exact h0
  rw [this, map_zero]

omit [IsAlgClosed k] [DecidableEq k] in
theorem fstPart_nonneg {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W) (W : PlF) : 0 ≤ P.fstPart E W := by
  classical
  unfold PlaceSpecialization.fstPart
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

omit [IsAlgClosed k] [DecidableEq k] in
theorem sndPart_nonneg {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W) (W : PlF) : 0 ≤ P.sndPart E W := by
  classical
  unfold PlaceSpecialization.sndPart
  rw [Finsupp.filter_apply]
  split_ifs
  · exact hE W
  · exact le_rfl

omit [IsAlgClosed k] [DecidableEq k] in
theorem neg_fstPart_le {E D : Divisor Qb Fq} (h : -E ≤ D) : -P.fstPart E ≤ P.fstPart D := by
  classical
  intro W
  unfold PlaceSpecialization.fstPart
  rw [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · exact h W
  · simp

omit [IsAlgClosed k] [DecidableEq k] in
theorem neg_sndPart_le {E D : Divisor Qb Fq} (h : -E ≤ D) : -P.sndPart E ≤ P.sndPart D := by
  classical
  intro W
  unfold PlaceSpecialization.sndPart
  rw [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply, Finsupp.filter_apply]
  split_ifs
  · exact h W
  · simp

omit [IsAlgClosed k] [DecidableEq k] in

theorem neg_le_ord_of_mem {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W) {f : Fq} (hf : f ∈ riemannRochSpace E)
    (W : PlF) : -E W ≤ W.ord f := by
  rcases (mem_riemannRochSpace_iff.mp hf) W with h0 | h
  · rw [h0, Place.ord_zero]; have := hE W; omega
  · exact h

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem image_fst_of_not_fixed (hDL : R.DivisorLawFst) {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W)
    {f : Fq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Plk) (hv : φ (φ v) ≠ v) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.redFst (P.fstPart E) v) ≤ v.ord (R.residue₁ ⟨f, h₁⟩ : Ck) := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (ResidueField A) := inferInstance
  obtain ⟨a, hne₁, hne₂⟩ := FltWs24.Perturb.exists_add_algebraMap_residue_ne_zero R.R₁ R.R₂ h₁ h₂
  have h₁' : f + algebraMap Qb Fq (a : Qb) ∈ R.R₁.integers :=
    add_mem h₁ (FltWs24.Perturb.algebraMap_mem_integers R.R₁ a)
  have h₂' : f + algebraMap Qb Fq (a : Qb) ∈ R.R₂.integers :=
    add_mem h₂ (FltWs24.Perturb.algebraMap_mem_integers R.R₂ a)
  have hf'E : f + algebraMap Qb Fq (a : Qb) ∈ riemannRochSpace E :=
    add_mem hf (FltWs24.Perturb.algebraMap_mem_riemannRochSpace hE _)
  have hf'0 : f + algebraMap Qb Fq (a : Qb) ≠ 0 := ne_zero_of_residue₁_ne_zero R h₁' hne₁
  obtain ⟨D, hD⟩ := FltWs24.DivTools.exists_principalDivisor _ hf'0
  have hlaw := hDL _ h₁' h₂' hne₁ hne₂ D hD v hv
  have hlaw' : Finsupp.mapDomain P.redFst (P.fstPart D) v = v.ord (R.residue₁ ⟨_, h₁'⟩ : Ck) := hlaw
  have hED : -E ≤ D := FltWs24.DivTools.neg_le_of_mem_riemannRochSpace hf'E hf'0 hD
  have hb := FltWs24.DivTools.neg_mapDomain_apply_le P.redFst (neg_fstPart_le (P := P) hED) v
  rw [hlaw'] at hb
  have e1 := FltWs24.Perturb.residue_add_algebraMap R.R₁ h₁ a
  have e2 : R.ι (R.R₁.residue ⟨_, h₁'⟩)
      = R.ι (R.R₁.residue ⟨f, h₁⟩) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [← ι_algebraMap, ← map_add]
    exact congrArg R.ι e1
  have hres : (R.residue₁ ⟨_, h₁'⟩ : Ck)
      = (R.residue₁ ⟨f, h₁⟩ : Ck) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [LevelOneProlongationPair.residue₁_apply, LevelOneProlongationPair.residue₁_apply]
    exact e2
  rw [hres] at hb
  have hn : -(Finsupp.mapDomain P.redFst (P.fstPart E) v) ≤ 0 := by
    have := mapDomain_nonneg_apply P.redFst (fstPart_nonneg (P := P) hE) v
    omega
  have key := FltWs24.Perturb.ord_add_algebraMap_ge_of_ge v hn (Or.inr hb)
    (-(R.redBar (IsLocalRing.residue A a)))
  rwa [map_neg, add_neg_cancel_right] at key

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem image_snd_of_not_fixed (hDL : R.DivisorLawSnd) {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W)
    {f : Fq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Plk) (hv : φ (φ v) ≠ v) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.redSnd (P.sndPart E) v) ≤ v.ord (R.residue₂ ⟨f, h₂⟩ : Ck) := by
  classical
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : Infinite (ResidueField A) := inferInstance
  obtain ⟨a, hne₁, hne₂⟩ := FltWs24.Perturb.exists_add_algebraMap_residue_ne_zero R.R₁ R.R₂ h₁ h₂
  have h₁' : f + algebraMap Qb Fq (a : Qb) ∈ R.R₁.integers :=
    add_mem h₁ (FltWs24.Perturb.algebraMap_mem_integers R.R₁ a)
  have h₂' : f + algebraMap Qb Fq (a : Qb) ∈ R.R₂.integers :=
    add_mem h₂ (FltWs24.Perturb.algebraMap_mem_integers R.R₂ a)
  have hf'E : f + algebraMap Qb Fq (a : Qb) ∈ riemannRochSpace E :=
    add_mem hf (FltWs24.Perturb.algebraMap_mem_riemannRochSpace hE _)
  have hf'0 : f + algebraMap Qb Fq (a : Qb) ≠ 0 := ne_zero_of_residue₁_ne_zero R h₁' hne₁
  obtain ⟨D, hD⟩ := FltWs24.DivTools.exists_principalDivisor _ hf'0
  have hlaw := hDL _ h₁' h₂' hne₁ hne₂ D hD v hv
  have hlaw' : Finsupp.mapDomain P.redSnd (P.sndPart D) v = v.ord (R.residue₂ ⟨_, h₂'⟩ : Ck) := hlaw
  have hED : -E ≤ D := FltWs24.DivTools.neg_le_of_mem_riemannRochSpace hf'E hf'0 hD
  have hb := FltWs24.DivTools.neg_mapDomain_apply_le P.redSnd (neg_sndPart_le (P := P) hED) v
  rw [hlaw'] at hb
  have e1 := FltWs24.Perturb.residue_add_algebraMap R.R₂ h₂ a
  have e2 : R.ι (R.R₂.residue ⟨_, h₂'⟩)
      = R.ι (R.R₂.residue ⟨f, h₂⟩) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [← ι_algebraMap, ← map_add]
    exact congrArg R.ι e1
  have hres : (R.residue₂ ⟨_, h₂'⟩ : Ck)
      = (R.residue₂ ⟨f, h₂⟩ : Ck) + algebraMap k Ck (R.redBar (IsLocalRing.residue A a)) := by
    rw [LevelOneProlongationPair.residue₂_apply, LevelOneProlongationPair.residue₂_apply]
    exact e2
  rw [hres] at hb
  have hn : -(Finsupp.mapDomain P.redSnd (P.sndPart E) v) ≤ 0 := by
    have := mapDomain_nonneg_apply P.redSnd (sndPart_nonneg (P := P) hE) v
    omega
  have key := FltWs24.Perturb.ord_add_algebraMap_ge_of_ge v hn (Or.inr hb)
    (-(R.redBar (IsLocalRing.residue A a)))
  rwa [map_neg, add_neg_cancel_right] at key

open Classical in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem image_fst_cusp {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W)
    {f : Fq} (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ R.R₁.integers) :
    (R.residue₁ ⟨f, h₁⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))))
        ≤ (P.redFst (cuspInftyBar (1 * q))).ord (R.residue₁ ⟨f, h₁⟩ : Ck) := by
  by_cases hne : R.R₁.residue ⟨f, h₁⟩ = 0
  · exact Or.inl (residue₁_coe_eq_zero R h₁ hne)
  right
  have hf0 : f ≠ 0 := ne_zero_of_residue₁_ne_zero R h₁ hne
  obtain ⟨D, hD⟩ := FltWs24.DivTools.exists_principalDivisor f hf0
  have hlaw := LevelOneProlongationPair.cuspLawInfty_oneSided R f h₁ hne D hD
  have hED : -E ≤ D := FltWs24.DivTools.neg_le_of_mem_riemannRochSpace hf hf0 hD
  have hb := FltWs24.DivTools.neg_mapDomain_filter_apply_le P.redFst P.IsInftySide hED
    (P.redFst (cuspInftyBar (1 * q)))
  rw [hlaw] at hb
  exact hb

open Classical in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem image_snd_cusp {E : Divisor Qb Fq} (hE : ∀ W, 0 ≤ E W)
    {f : Fq} (hf : f ∈ riemannRochSpace E) (h₂ : f ∈ R.R₂.integers) :
    (R.residue₂ ⟨f, h₂⟩ : Ck) = 0 ∨
      -(Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))))
        ≤ (P.redSnd (cuspZeroBar (1 * q))).ord (R.residue₂ ⟨f, h₂⟩ : Ck) := by
  by_cases hne : R.R₂.residue ⟨f, h₂⟩ = 0
  · exact Or.inl (residue₂_coe_eq_zero R h₂ hne)
  right
  have hf0 : f ≠ 0 := ne_zero_of_residue₂_ne_zero R h₂ hne
  obtain ⟨D, hD⟩ := FltWs24.DivTools.exists_principalDivisor f hf0
  have hlaw := LevelOneProlongationPair.cuspLawZero_oneSided R f h₂ hne D hD
  have hED : -E ≤ D := FltWs24.DivTools.neg_le_of_mem_riemannRochSpace hf hf0 hD
  have hb := FltWs24.DivTools.neg_mapDomain_filter_apply_le P.redSnd P.IsZeroSide hED
    (P.redSnd (cuspZeroBar (1 * q)))
  rw [hlaw] at hb
  exact hb

omit [IsAlgClosed k] in
theorem five_le_of_ss_ne {a : k} (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h0 : a ≠ 0) : 5 ≤ q := by
  have hp : q.Prime := Fact.out
  by_contra hlt
  push_neg at hlt
  have h2 := hp.two_le
  have hcase : q = 2 ∨ q = 3 ∨ q = 4 := by omega
  rcases hcase with hq | hq | hq
  · subst hq
    exact h0 (ModularCurve.eq_zero_of_mem_ssJSet_two a ha ha2)
  · subst hq
    exact h0 (ModularCurve.eq_zero_of_mem_ssJSet_three a ha ha2)
  · subst hq
    exact absurd hp (by decide)

end SiteC

end FltWs24.Asm

namespace FltWs24
namespace Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section SiteE

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

local notation "Qb" => AlgebraicClosure ℚ
local notation "Fq" => modularFunctionFieldBar (1 * q)
local notation "Ck" => modularFunctionFieldC k 1
local notation "Plk" => Place k (modularFunctionFieldC k 1)
local notation "PlF" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

omit [DecidableEq k] in
theorem deg_one_k (w : Plk) : w.deg = 1 := ModularCurve.place_deg_eq_one_of_isAlgClosed k 1 w

omit [IsAlgClosed k] [DecidableEq k] in
theorem deg_one_Q (W : PlF) : W.deg = 1 :=
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  ModularCurve.deg_eq_one_modularFunctionFieldBar (1 * q) W

omit [IsAlgClosed k] [DecidableEq k] in
set_option maxHeartbeats 1600000 in

theorem not_strictTwo_of_strictOne {W : PlF} (h1 : P.IsStrictTypeOne W) : ¬ P.IsStrictTypeTwo W := by
  intro h2
  apply h1.2
  have e1 := h1.1
  have e2 := h2.1

  rw [e1] ; exact e2.symm

open Classical in
set_option maxHeartbeats 3200000 in

theorem degree_E_split (E : Divisor Qb Fq) :
    Divisor.degree E
      = (∑ W ∈ E.support.filter P.IsStrictTypeOne, E W)
        + (∑ W ∈ E.support.filter P.IsStrictTypeTwo, E W)
        + (∑ v ∈ (E.support.image P.redFst).filter (fun v => φ (φ v) = v), Finsupp.mapDomain P.redFst E v) := by
  classical
  rw [degree_eq_sum_support_of_deg_eq_one deg_one_Q E,
    ← Finset.sum_filter_add_sum_filter_not E.support (fun W => φ (φ (P.redFst W)) = P.redFst W)]

  have hnf : (∑ W ∈ E.support.filter (fun W => ¬ φ (φ (P.redFst W)) = P.redFst W), E W)
      = (∑ W ∈ E.support.filter P.IsStrictTypeOne, E W) + (∑ W ∈ E.support.filter P.IsStrictTypeTwo, E W) := by
    rw [← Finset.sum_filter_add_sum_filter_not (E.support.filter _) P.IsStrictTypeOne,
      Finset.filter_filter, Finset.filter_filter]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun _ _ => rfl)
      exact ⟨fun h => h.2, fun h => ⟨h.2, h⟩⟩
    · refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun _ _ => rfl)
      constructor
      · rintro ⟨hnf, hn1⟩
        rcases ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne P W |>.mpr hnf with h | h
        · exact absurd h hn1
        · exact h
      · intro h2
        refine ⟨(ModularCurve.PlaceSpecialization.isStrictTypeOne_or_isStrictTypeTwo_iff_ne P W).mp (Or.inr h2),
          fun h1 => not_strictTwo_of_strictOne h1 h2⟩

  have hfx : (∑ W ∈ E.support.filter (fun W => φ (φ (P.redFst W)) = P.redFst W), E W)
      = ∑ v ∈ (E.support.image P.redFst).filter (fun v => φ (φ v) = v), Finsupp.mapDomain P.redFst E v := by
    have hmaps : ∀ W ∈ E.support.filter (fun W => φ (φ (P.redFst W)) = P.redFst W),
        P.redFst W ∈ (E.support.image P.redFst).filter (fun v => φ (φ v) = v) := by
      intro W hW
      rw [Finset.mem_filter] at hW ⊢
      exact ⟨Finset.mem_image_of_mem _ hW.1, hW.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun W => E W)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.mem_filter] at hv
    rw [mapDomain_apply_eq_sum_filter, Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun _ _ => rfl)
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hv.2, h⟩⟩
  rw [hnf, hfx]
  ring

open Classical in
set_option maxHeartbeats 3200000 in

theorem mass_cusp (E : Divisor Qb Fq) :
    Finsupp.mapDomain P.redFst E (P.redFst (cuspInftyBar (1 * q)))
      = Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q)))
        + Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) := by
  rw [mapDomain_apply_eq_sum_filter, mapDomain_apply_eq_sum_filter, mapDomain_apply_eq_sum_filter,
    Finsupp.support_filter, Finsupp.support_filter, Finset.filter_filter, Finset.filter_filter]

  have h1 : (∑ W ∈ E.support.filter (fun W => P.IsInftySide W ∧ P.redFst W = P.redFst (cuspInftyBar (1 * q))),
      (E.filter P.IsInftySide) W) = ∑ W ∈ E.support.filter P.IsInftySide, E W := by
    refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun W hW => ?_)
    · exact ⟨fun h => h.1, fun h => ⟨h, FltWs24.PlaceDict.redFst_eq_of_isCuspidal P W h.1⟩⟩
    · rw [Finset.mem_filter] at hW
      rw [Finsupp.filter_apply, if_pos hW.2]
  have h2 : (∑ W ∈ E.support.filter (fun W => P.IsZeroSide W ∧ P.redSnd W = P.redSnd (cuspZeroBar (1 * q))),
      (E.filter P.IsZeroSide) W) = ∑ W ∈ E.support.filter P.IsZeroSide, E W := by
    refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun W hW => ?_)
    · exact ⟨fun h => h.1, fun h => ⟨h, FltWs24.PlaceDict.redSnd_eq_of_isZeroSide P W h⟩⟩
    · rw [Finset.mem_filter] at hW
      rw [Finsupp.filter_apply, if_pos hW.2]
  rw [h1, h2]

  have hc : E.support.filter (fun W => P.redFst W = P.redFst (cuspInftyBar (1 * q)))
      = E.support.filter P.IsCuspidal :=
    Finset.filter_congr fun W _ =>
      ⟨fun h => FltWs24.PlaceDict.isCuspidal_of_redFst_eq P W h,
        fun h => FltWs24.PlaceDict.redFst_eq_of_isCuspidal P W h⟩
  rw [hc, ← Finset.sum_filter_add_sum_filter_not (E.support.filter P.IsCuspidal) P.IsInftySide,
    Finset.filter_filter, Finset.filter_filter]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun _ _ => rfl)
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  · refine Finset.sum_congr (Finset.filter_congr fun W _ => ?_) (fun _ _ => rfl)
    constructor
    · rintro ⟨hc, hni⟩
      rcases ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal P W hc with h | h
      · exact absurd h hni
      · exact h
    · intro hz
      exact ⟨FltWs24.PlaceDict.isCuspidal_of_isZeroSide P W hz, ModularCurve.not_isInftySide_of_isZeroSide P W hz⟩

open Classical in

theorem degree_fstPart_push (E : Divisor Qb Fq) :
    Divisor.degree (Finsupp.mapDomain P.redFst (P.fstPart E)) = ∑ W ∈ E.support.filter P.IsStrictTypeOne, E W := by
  rw [degree_eq_sum_of_deg_eq_one deg_one_k, sum_mapDomain_id, ← degree_eq_sum_of_deg_eq_one deg_one_Q]
  unfold PlaceSpecialization.fstPart
  rw [degree_filter_eq_sum deg_one_Q]

open Classical in
set_option maxHeartbeats 1600000 in
theorem degree_sndPart_push (E : Divisor Qb Fq) :
    Divisor.degree (Finsupp.mapDomain P.redSnd (P.sndPart E)) = ∑ W ∈ E.support.filter P.IsStrictTypeTwo, E W := by
  rw [degree_eq_sum_of_deg_eq_one deg_one_k, sum_mapDomain_id, ← degree_eq_sum_of_deg_eq_one deg_one_Q]
  unfold PlaceSpecialization.sndPart
  rw [degree_filter_eq_sum deg_one_Q]

open Classical in
set_option maxHeartbeats 1600000 in
theorem degree_D1 (E : Divisor Qb Fq) (Vfix : Finset Plk) (s : Plk → ℤ) (Sm : Finset k) (n₁ : k → ℕ) :
    Divisor.degree (D1 P E Vfix s Sm n₁)
      = (∑ W ∈ E.support.filter P.IsStrictTypeOne, E W) + (∑ v ∈ Vfix, -s v) + (∑ a ∈ Sm, (n₁ a : ℤ))
        + Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) := by
  have e2 : Divisor.degree (∑ v ∈ Vfix, Finsupp.single v (-s v)) = ∑ v ∈ Vfix, -s v :=
    degree_sum_single_of_deg_eq_one deg_one_k Vfix (fun v => v) (fun v => -s v)
  have e3 : Divisor.degree (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).1 (n₁ a : ℤ)) = ∑ a ∈ Sm, (n₁ a : ℤ) :=
    degree_sum_single_of_deg_eq_one deg_one_k Sm (fun a => (frobNodePair q a).1) (fun a => (n₁ a : ℤ))
  rw [D1, map_add, map_add, map_add, degree_fstPart_push, e2, e3, degree_single_of_deg_eq_one deg_one_k]

open Classical in
set_option maxHeartbeats 1600000 in
theorem degree_D2 (E : Divisor Qb Fq) (Vfix : Finset Plk) (s : Plk → ℤ) (Sm : Finset k) (n₂ : k → ℕ) :
    Divisor.degree (D2 P E Vfix s Sm n₂)
      = (∑ W ∈ E.support.filter P.IsStrictTypeTwo, E W)
        + (∑ v ∈ Vfix, (Finsupp.mapDomain P.redFst E v + s v)) + (∑ a ∈ Sm, (n₂ a : ℤ))
        + Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) := by
  have e2 : Divisor.degree (∑ v ∈ Vfix, Finsupp.single (φ v) (Finsupp.mapDomain P.redFst E v + s v))
      = ∑ v ∈ Vfix, (Finsupp.mapDomain P.redFst E v + s v) :=
    degree_sum_single_of_deg_eq_one deg_one_k Vfix (fun v => φ v) (fun v => Finsupp.mapDomain P.redFst E v + s v)
  have e3 : Divisor.degree (∑ a ∈ Sm, Finsupp.single (frobNodePair q a).2 (n₂ a : ℤ)) = ∑ a ∈ Sm, (n₂ a : ℤ) :=
    degree_sum_single_of_deg_eq_one deg_one_k Sm (fun a => (frobNodePair q a).2) (fun a => (n₂ a : ℤ))
  rw [D2, map_add, map_add, map_add, degree_sndPart_push, e2, e3, degree_single_of_deg_eq_one deg_one_k]

open Classical in
set_option maxHeartbeats 3200000 in

theorem degree_identity (E : Divisor Qb Fq) (Vfix : Finset Plk) (s : Plk → ℤ) (Sm : Finset k)
    (n₁ n₂ : k → ℕ)
    (hVfix : ∀ v, v ∈ Vfix ↔ v ∈ E.support.image P.redFst ∧ φ (φ v) = v ∧
      v ≠ P.redFst (cuspInftyBar (1 * q)) ∧ ∀ a ∈ Sm, v ≠ (frobNodePair q a).1)
    (hSmW : ∀ a ∈ Sm, (frobNodePair q a).1 ∈ E.support.image P.redFst)
    (hsq : ∀ a ∈ Sm, a ^ (q ^ 2) = a)
    (hmass : ∀ a ∈ Sm, ((n₁ a : ℤ) + n₂ a = Finsupp.mapDomain P.redFst E (frobNodePair q a).1)) :
    Divisor.degree (D1 P E Vfix s Sm n₁) + Divisor.degree (D2 P E Vfix s Sm n₂) = Divisor.degree E := by
  classical
  rw [degree_D1, degree_D2, degree_E_split (P := P) E]

  set T : Finset Plk := (E.support.image P.redFst).filter (fun v => φ (φ v) = v) with hT
  have hm0 : ∀ v : Plk, v ∉ E.support.image P.redFst → Finsupp.mapDomain P.redFst E v = 0 := fun v hvi =>
    mapDomain_apply_eq_zero_of_forall _ _ _ (fun W hW h => hvi (Finset.mem_image.mpr ⟨W, hW, h⟩))
  have hsplit : (∑ v ∈ T, Finsupp.mapDomain P.redFst E v)
      = (∑ v ∈ T.filter (fun v => v ≠ P.redFst (cuspInftyBar (1 * q))), Finsupp.mapDomain P.redFst E v)
        + Finsupp.mapDomain P.redFst E (P.redFst (cuspInftyBar (1 * q))) := by
    rw [← Finset.sum_filter_add_sum_filter_not T (fun v => v ≠ P.redFst (cuspInftyBar (1 * q)))]
    suffices hsuf : (∑ v ∈ T.filter (fun v => ¬ v ≠ P.redFst (cuspInftyBar (1 * q))), Finsupp.mapDomain P.redFst E v)
        = Finsupp.mapDomain P.redFst E (P.redFst (cuspInftyBar (1 * q))) by
      rw [hsuf]
    by_cases hin : P.redFst (cuspInftyBar (1 * q)) ∈ T
    · have : T.filter (fun v => ¬ v ≠ P.redFst (cuspInftyBar (1 * q))) = {P.redFst (cuspInftyBar (1 * q))} := by
        ext v
        simp only [Finset.mem_filter, Finset.mem_singleton, not_not]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hin, h⟩⟩
      rw [this, Finset.sum_singleton]
    · have : T.filter (fun v => ¬ v ≠ P.redFst (cuspInftyBar (1 * q))) = ∅ :=
        Finset.filter_eq_empty_iff.mpr (fun v hv h => hin ((not_not.mp h) ▸ hv))
      rw [this, Finset.sum_empty, hm0]
      intro h
      exact hin (Finset.mem_filter.mpr ⟨h, by
        rw [FltWs24.PlaceDict.frob_redFst_cuspInftyBar P, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P]⟩)

  have hfin : (∑ v ∈ T.filter (fun v => v ≠ P.redFst (cuspInftyBar (1 * q))), Finsupp.mapDomain P.redFst E v)
      = (∑ v ∈ Vfix, Finsupp.mapDomain P.redFst E v)
        + ∑ a ∈ Sm, Finsupp.mapDomain P.redFst E (frobNodePair q a).1 := by
    rw [← Finset.sum_image (f := fun v => Finsupp.mapDomain P.redFst E v)
      (s := Sm) (g := fun a => (frobNodePair q a).1) (fun a _ b _ h => np1_injective h),
      ← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext v
      rw [Finset.mem_filter, Finset.mem_union, hVfix, hT, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hvi, hvf⟩, hvc⟩
        by_cases hn : ∃ a ∈ Sm, (frobNodePair q a).1 = v
        · exact Or.inr (Finset.mem_image.mpr hn)
        · push_neg at hn
          exact Or.inl ⟨hvi, hvf, hvc, fun a ha h => hn a ha h.symm⟩
      · rintro (⟨hvi, hvf, hvc, -⟩ | hv')
        · exact ⟨⟨hvi, hvf⟩, hvc⟩
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv'
          exact ⟨⟨hSmW a ha, frob_frob_np1 a (hsq a ha)⟩, FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a⟩
    · rw [Finset.disjoint_left]
      intro v hv hv'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv'
      exact ((hVfix _).mp hv).2.2.2 a ha rfl
  rw [hsplit, hfin, mass_cusp (P := P) E, ← Finset.sum_congr rfl (fun a ha => hmass a ha),
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_neg_distrib]
  ring

end SiteE

end FltWs24.Asm

namespace FltWs24
namespace Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

section SiteD

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

local notation "Qb" => AlgebraicClosure ℚ
local notation "Fq" => modularFunctionFieldBar (1 * q)
local notation "Ck" => modularFunctionFieldC k 1
local notation "Plk" => Place k (modularFunctionFieldC k 1)
local notation "PlF" => Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))
local notation "φ" => frobOnPlacesGeomLevel k 1 data hKr

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem splitDatum_of_forall_centred_ord_eq_main (R : P.LevelOneProlongationPair)
    (hR : R.IsModel) (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : ∀ W, 0 ≤ E W)
    (hEsupp : ∀ W ∈ E.support, P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W ∨
      ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (t : ↥(modularFunctionFieldBar (1 * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (htord : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord t = E W)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.redFst E (frobNodePair q a).1)
    (htw₁ : (frobNodePair q a).1.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ (-(n₁ : ℤ))
        * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k 1))) l₁)
    (htw₂ : (frobNodePair q a).2.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k 1))) l₂) :
    R.SplitDatum S₀ E
      (Finsupp.mapDomain P.redFst (P.fstPart E) + Finsupp.single (frobNodePair q a).1 (n₁ : ℤ))
      (Finsupp.mapDomain P.redSnd (P.sndPart E) + Finsupp.single (frobNodePair q a).2 (n₂ : ℤ))
      (Function.update (fun _ => (1 : k)) a (l₂ * l₁⁻¹)) := by
  classical
  haveI : NeZero (1 * q) := ⟨by rw [one_mul]; exact (Fact.out : q.Prime).ne_zero⟩
  haveI hAC : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hφinj : Function.Injective (frobOnPlacesGeomLevel k 1 data hKr) := frobOnPlacesGeomLevel_injective k 1 data hKr

  have hν1fix : φ (φ (frobNodePair q a).1) = (frobNodePair q a).1 := frob_frob_np1 a ha2
  have hν1c : (frobNodePair q a).1 ≠ P.redFst (cuspInftyBar (1 * q)) :=
    FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a

  have hsuppfix : ∀ W ∈ E.support, φ (φ (P.redFst W)) = P.redFst W → P.redFst W = (frobNodePair q a).1 := by
    intro W hW hfix
    rcases hEsupp W hW with h1 | h2 | hc
    · exact absurd hfix h1.2
    · exfalso
      apply h2.2
      apply hφinj
      have h := hfix
      rw [h2.1] at h
      exact h
    · exact (FltWs24.PlaceDict.redFst_eq_frobNodePair_iff P W a ha2).mpr hc

  set Sm : Finset k := ({a} : Finset k).filter (fun a' => ∃ W ∈ E.support, P.redFst W = (frobNodePair q a').1)
    with hSm
  have hSma : ∀ a' ∈ Sm, a' = a := fun a' ha' => Finset.mem_singleton.mp (Finset.mem_filter.mp ha').1
  have hSmW : ∀ a' ∈ Sm, ∃ W ∈ E.support, P.redFst W = (frobNodePair q a').1 := fun a' ha' =>
    (Finset.mem_filter.mp ha').2
  have haSm : (∃ W ∈ E.support, P.redFst W = (frobNodePair q a).1) → a ∈ Sm := fun h =>
    Finset.mem_filter.mpr ⟨Finset.mem_singleton_self a, h⟩
  have H : IndexHyp P (∅ : Finset Plk) Sm :=
    { fixV := fun v hv => absurd hv (Finset.notMem_empty v)
      neV := fun v hv => absurd hv (Finset.notMem_empty v)
      notNode := fun v hv => absurd hv (Finset.notMem_empty v)
      sq := fun a' ha' => by rw [hSma a' ha']; exact ha2 }

  have hm0 : ∀ v : Plk, φ (φ v) = v → (∀ a' ∈ Sm, v ≠ (frobNodePair q a').1) →
      Finsupp.mapDomain P.redFst E v = 0 := by
    intro v hv hvn
    apply mapDomain_apply_eq_zero_of_forall
    intro W hW h
    have hWν : P.redFst W = (frobNodePair q a).1 := hsuppfix W hW (by rw [h]; exact hv)
    exact hvn a (haSm ⟨W, hW, hWν⟩) (by rw [← h, hWν])
  have hmass : ∀ a' ∈ Sm, ((n₁ : ℤ) + n₂ = Finsupp.mapDomain P.redFst E (frobNodePair q a').1) := by
    intro a' ha'
    rw [hSma a' ha']
    exact hn

  have hn0 : a ∉ Sm → n₁ = 0 ∧ n₂ = 0 := by
    intro haS
    have h0 : Finsupp.mapDomain P.redFst E (frobNodePair q a).1 = 0 :=
      mapDomain_apply_eq_zero_of_forall _ _ _ (fun W hW h => haS (haSm ⟨W, hW, h⟩))
    rw [h0] at hn
    omega

  have hD1ν : D1 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₁) (frobNodePair q a).1 = n₁ := by
    by_cases haS : a ∈ Sm
    · exact D1_node H haS
    · have hvn : ∀ a' ∈ Sm, (frobNodePair q a).1 ≠ (frobNodePair q a').1 :=
        fun a' ha' _ => haS ((hSma a' ha') ▸ ha')
      rw [D1_of_fixed_else H _ hν1fix hν1c hvn (Finset.notMem_empty _), (hn0 haS).1]
      simp
  have hD2ν : D2 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₂) (frobNodePair q a).2 = n₂ := by
    by_cases haS : a ∈ Sm
    · exact D2_node H haS
    · have hvn : ∀ a' ∈ Sm, (frobNodePair q a).1 ≠ (frobNodePair q a').1 :=
        fun a' ha' _ => haS ((hSma a' ha') ▸ ha')
      rw [← frob_np1 (data := data) (hKr := hKr) a,
        D2_of_fixed_else H _ hν1fix hν1c hvn (Finset.notMem_empty _), (hn0 haS).2]
      simp

  have hD1fix : ∀ v : Plk, φ (φ v) = v → v ≠ P.redFst (cuspInftyBar (1 * q)) →
      v ≠ (frobNodePair q a).1 → D1 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₁) v = 0 := by
    intro v hv hvc hvn
    exact D1_of_fixed_else H v hv hvc (fun a' ha' h => hvn (by rw [h, hSma a' ha'])) (Finset.notMem_empty v)
  have hD2fix : ∀ v : Plk, φ (φ v) = v → v ≠ P.redFst (cuspInftyBar (1 * q)) →
      v ≠ (frobNodePair q a).1 → D2 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₂) (φ v) = 0 := by
    intro v hv hvc hvn
    exact D2_of_fixed_else H v hv hvc (fun a' ha' h => hvn (by rw [h, hSma a' ha'])) (Finset.notMem_empty v)
  have hm0' : ∀ v : Plk, φ (φ v) = v → v ≠ (frobNodePair q a).1 → Finsupp.mapDomain P.redFst E v = 0 :=
    fun v hv hvn => hm0 v hv (fun a' ha' h => hvn (by rw [h, hSma a' ha']))

  have hordfix : ∀ {f : Fq}, f ∈ riemannRochSpace E → ∀ v : Plk, φ (φ v) = v → v ≠ (frobNodePair q a).1 →
      ∀ W : PlF, P.redFst W = v → 0 ≤ W.ord f := by
    intro f hf v hv hvn W hWv
    have hEW : E W = 0 := by
      by_contra hne
      exact hvn (hWv ▸ hsuppfix W (Finsupp.mem_support_iff.mpr hne) (by rw [hWv]; exact hv))
    have := neg_le_ord_of_mem hE0 hf W
    rw [hEW, neg_zero] at this
    exact this

  have hfE : ∀ {f : Fq}, f ∈ riemannRochSpace E → ∀ W : PlF, -E W ≤ W.ord f := fun hf W =>
    neg_le_ord_of_mem hE0 hf W

  have hspec : ∀ (f : Fq), f ∈ riemannRochSpace E → ∀ (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers),
      (R.residue₁ ⟨f, h₁⟩ ≠ 0 → -(n₁ : ℤ) ≤ (frobNodePair q a).1.ord (R.residue₁ ⟨f, h₁⟩ : Ck)) ∧
      (R.residue₂ ⟨f, h₂⟩ ≠ 0 → -(n₂ : ℤ) ≤ (frobNodePair q a).2.ord (R.residue₂ ⟨f, h₂⟩ : Ck)) ∧
      ∃ c : k,
        (frobNodePair q a).1.HasValue
          (((⟨jqModC k, jqModC_mem k 1⟩ : Ck) - algebraMap k Ck a) ^ (n₁ : ℤ)
            * (R.residue₁ ⟨f, h₁⟩ : Ck)) (l₂ * c) ∧
        (frobNodePair q a).2.HasValue
          (((⟨jqModC k, jqModC_mem k 1⟩ : Ck) - algebraMap k Ck (a ^ q)) ^ (n₂ : ℤ)
            * (R.residue₂ ⟨f, h₂⟩ : Ck)) (l₁ * c) := by
    intro f hf h₁ h₂
    refine R.le_ord_residue_and_exists_hasValue_of_mul a ha ha2 f t h₁ h₂ ht₁ ht₂ ?_ (n₁ : ℤ) (n₂ : ℤ)
      l₁ l₂ hl₁ hl₂ htw₁ htw₂
    intro W hW
    by_cases hft : f * t = 0
    · rw [hft, Place.ord_zero]
    · have hf0 : f ≠ 0 := fun h => hft (by rw [h, zero_mul])
      have ht0 : t ≠ 0 := fun h => hft (by rw [h, mul_zero])
      rw [Place.ord_mul W hf0 ht0, htord W hW]
      have := hfE hf W
      omega

  have hcm1 : Finsupp.mapDomain P.redFst (E.filter P.IsInftySide) (P.redFst (cuspInftyBar (1 * q))) = 0 := by
    apply mapDomain_apply_eq_zero_of_forall
    intro W hW h
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    have := hsuppfix W hW.1 (by rw [h]; exact cusp_fixed P)
    exact hν1c (this ▸ h)
  have hcm2 : Finsupp.mapDomain P.redSnd (E.filter P.IsZeroSide) (P.redSnd (cuspZeroBar (1 * q))) = 0 := by
    apply mapDomain_apply_eq_zero_of_forall
    intro W hW h
    rw [Finsupp.support_filter, Finset.mem_filter] at hW
    rw [cusp0_eq P] at h
    rcases hEsupp W hW.1 with h1 | h2 | hc
    · apply h1.2
      apply hφinj
      rw [h1.1, h, cusp_fixed P]
    · exact h2.2 (by rw [h, cusp_fixed P])
    · obtain ⟨x, -, hx⟩ := hc.1
      have hcusp := FltWs24.PlaceDict.isCuspidal_of_isZeroSide P W hW.2 x
      exact absurd hx (not_lt.mpr hcusp)

  have hD1eq : D1 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₁)
      = Finsupp.mapDomain P.redFst (P.fstPart E) + Finsupp.single (frobNodePair q a).1 (n₁ : ℤ) := by
    unfold D1
    rw [hcm1, Finsupp.single_zero, add_zero, Finset.sum_empty, add_zero]
    by_cases haS : a ∈ Sm
    · have : Sm = {a} := Finset.eq_singleton_iff_unique_mem.mpr ⟨haS, hSma⟩
      rw [this, Finset.sum_singleton]
    · have : Sm = ∅ := Finset.eq_empty_of_forall_notMem (fun a' ha' => haS ((hSma a' ha') ▸ ha'))
      rw [this, Finset.sum_empty, (hn0 haS).1, Nat.cast_zero, Finsupp.single_zero]
  have hD2eq : D2 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₂)
      = Finsupp.mapDomain P.redSnd (P.sndPart E) + Finsupp.single (frobNodePair q a).2 (n₂ : ℤ) := by
    unfold D2
    rw [hcm2, Finsupp.single_zero, add_zero, Finset.sum_empty, add_zero]
    by_cases haS : a ∈ Sm
    · have : Sm = {a} := Finset.eq_singleton_iff_unique_mem.mpr ⟨haS, hSma⟩
      rw [this, Finset.sum_singleton]
    · have : Sm = ∅ := Finset.eq_empty_of_forall_notMem (fun a' ha' => haS ((hSma a' ha') ▸ ha'))
      rw [this, Finset.sum_empty, (hn0 haS).2, Nat.cast_zero, Finsupp.single_zero]
  rw [← hD1eq, ← hD2eq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv hvc
    rw [filter_eq_zero_of_nonneg E hE0 _ (fun W => Iff.rfl), Finsupp.mapDomain_zero, Finsupp.zero_apply,
      filter_eq_self_of_nonneg E hE0 _ (fun W => Iff.rfl)]
    by_cases hvn : v = (frobNodePair q a).1
    · subst hvn
      rw [hD1ν, frob_np1, hD2ν, ← hn]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · rw [hD1fix v hv hvc hvn, hD2fix v hv hvc hvn, hm0' v hv hvn]
      exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩
  ·
    have hSmWi : ∀ a' ∈ Sm, (frobNodePair q a').1 ∈ E.support.image P.redFst := fun a' ha' => by
      obtain ⟨W, hW, h⟩ := hSmW a' ha'
      exact Finset.mem_image.mpr ⟨W, hW, h⟩
    refine degree_identity E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₁) (fun _ => n₂) (fun v => ?_) hSmWi
      (fun a' ha' => H.sq a' ha') hmass
    simp only [Finset.notMem_empty, false_iff, not_and]
    intro hvi hv hvc hvn
    obtain ⟨W, hW, hWv⟩ := Finset.mem_image.mp hvi
    have hWν : P.redFst W = (frobNodePair q a).1 := hsuppfix W hW (by rw [hWv]; exact hv)
    exact hvn a (haSm ⟨W, hW, hWν⟩) (by rw [← hWv, hWν])
  ·
    intro a' _
    by_cases h : a' = a
    · rw [h, Function.update_self]
      exact mul_ne_zero hl₂ (inv_ne_zero hl₁)
    · rw [Function.update_of_ne h]
      exact one_ne_zero
  ·
    intro v hv
    exact ⟨D1_of_not_fixed H v hv, D2_of_not_fixed H v hv⟩
  ·
    intro v hv hvc
    by_cases hvn : v = (frobNodePair q a).1
    · subst hvn
      rw [hD1ν, frob_np1, hD2ν]
      exact hn
    · rw [hD1fix v hv hvc hvn, hD2fix v hv hvc hvn, hm0' v hv hvn, add_zero]
  ·
    exact D1_cusp H
  ·
    exact D2_cusp H
  ·
    intro f hf h₁ h₂
    refine ⟨?_, ?_, ?_⟩
    ·
      rw [mem_riemannRochSpace_iff]
      intro v
      by_cases hv : φ (φ v) = v
      · by_cases hvc : v = P.redFst (cuspInftyBar (1 * q))
        · rw [hvc, D1_cusp H]
          exact image_fst_cusp R hE0 hf h₁
        · by_cases hvn : v = (frobNodePair q a).1
          · subst hvn
            rw [hD1ν]
            by_cases h0 : (R.residue₁ ⟨f, h₁⟩ : Ck) = 0
            · exact Or.inl h0
            · exact Or.inr ((hspec f hf h₁ h₂).1 h0)
          · rw [hD1fix v hv hvc hvn, neg_zero]
            by_cases h0 : (R.residue₁ ⟨f, h₁⟩ : Ck) = 0
            · exact Or.inl h0
            · exact Or.inr ((hNR.1 f h₁ h₂ v hv hvc (hordfix hf v hv hvn)).1 h0)
      · rw [D1_of_not_fixed H v hv]
        exact image_fst_of_not_fixed R hR.1 hE0 hf h₁ h₂ v hv
    ·
      rw [mem_riemannRochSpace_iff]
      intro w
      by_cases hw : φ (φ w) = w
      · have hvfix : φ (φ (φ w)) = φ w := by rw [hw]
        by_cases hvc : φ w = P.redFst (cuspInftyBar (1 * q))
        · have hw0 : w = P.redSnd (cuspZeroBar (1 * q)) := by
            rw [← hw, hvc, FltWs24.PlaceDict.frob_redFst_cuspInftyBar P,
              FltWs24.PlaceDict.redSnd_cuspZeroBar_eq P]
          rw [hw0, D2_cusp H]
          exact image_snd_cusp R hE0 hf h₂
        · by_cases hvn : φ w = (frobNodePair q a).1
          · have hw2 : w = (frobNodePair q a).2 := by rw [← hw, hvn, frob_np1]
            rw [hw2, hD2ν]
            by_cases h0 : (R.residue₂ ⟨f, h₂⟩ : Ck) = 0
            · exact Or.inl h0
            · exact Or.inr ((hspec f hf h₁ h₂).2.1 h0)
          · rw [show D2 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₂) w
                = D2 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₂) (φ (φ w)) by rw [hw],
              hD2fix (φ w) hvfix hvc hvn, neg_zero]
            by_cases h0 : (R.residue₂ ⟨f, h₂⟩ : Ck) = 0
            · exact Or.inl h0
            · have key := (hNR.1 f h₁ h₂ (φ w) hvfix hvc (hordfix hf (φ w) hvfix hvn)).2 h0
              rw [hw] at key
              exact Or.inr key
      · rw [D2_of_not_fixed H w hw]
        exact image_snd_of_not_fixed R hR.2.1 hE0 hf h₁ h₂ w hw
    ·
      intro a' ha'S ha'2
      by_cases haa : a' = a
      · rw [haa]
        obtain ⟨c, hc₁, hc₂⟩ := (hspec f hf h₁ h₂).2.2
        refine ⟨l₁ * c, ?_, ?_⟩
        · rw [hD1ν, Function.update_self]
          have : l₂ * l₁⁻¹ * (l₁ * c) = l₂ * c := by
            field_simp [hl₁]
          rw [this]
          exact hc₁
        · rw [hD2ν]
          exact hc₂
      ·
        have ha' : a' ∈ ssJSet q k := (hS₀ a').mp ha'S
        have hνν : (frobNodePair q a').1 ≠ (frobNodePair q a).1 := fun h => haa (np1_injective h)
        have hfx : φ (φ (frobNodePair q a').1) = (frobNodePair q a').1 := frob_frob_np1 a' ha'2
        have hvc : (frobNodePair q a').1 ≠ P.redFst (cuspInftyBar (1 * q)) :=
          FltWs24.PlaceDict.frobNodePair_fst_ne_cusp P a'
        have hD1 : D1 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₁) (frobNodePair q a').1 = 0 :=
          hD1fix _ hfx hvc hνν
        have hD2 : D2 P E ∅ (fun _ => (0 : ℤ)) Sm (fun _ => n₂) (frobNodePair q a').2 = 0 := by
          rw [← frob_np1 (data := data) (hKr := hKr) a', hD2fix _ hfx hvc hνν]
        rw [hD1, hD2, Function.update_of_ne haa]
        have h1₁ : (1 : Fq) ∈ R.R₁.integers := R.R₁.integers.one_mem
        have h1₂ : (1 : Fq) ∈ R.R₂.integers := R.R₂.integers.one_mem
        have hr1 : (R.residue₁ ⟨1, h1₁⟩ : Ck) = 1 := by
          rw [show (⟨1, h1₁⟩ : R.R₁.integers) = 1 from rfl, map_one]
        have hr2 : (R.residue₂ ⟨1, h1₂⟩ : Ck) = 1 := by
          rw [show (⟨1, h1₂⟩ : R.R₂.integers) = 1 from rfl, map_one]
        obtain ⟨-, -, c, hc₁, hc₂⟩ := R.le_ord_residue_and_exists_hasValue_of_mul a' ha' ha'2 f 1
          h₁ h₂ h1₁ h1₂
          (fun W hW => by
            rw [mul_one]
            have hWv : P.redFst W = (frobNodePair q a').1 :=
              (FltWs24.PlaceDict.redFst_eq_frobNodePair_iff P W a' ha'2).mpr hW
            exact hordfix hf _ hfx hνν W hWv)
          0 0 1 1 one_ne_zero one_ne_zero
          (by rw [hr1, mul_one, neg_zero, zpow_zero]; exact Place.hasValue_one _)
          (by rw [hr2, mul_one, neg_zero, zpow_zero]; exact Place.hasValue_one _)
        refine ⟨c, ?_, ?_⟩
        · exact hc₁
        · rw [one_mul c] at hc₂
          exact hc₂

end SiteD

end FltWs24.Asm

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
open Classical in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hR : R.IsModel) (S₀ : Finset k) (hS₀ : ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q k) (hNR : R.RegularityLaw S₀)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hE0 : ∀ W, 0 ≤ E W)
    (hEsupp : ∀ W ∈ E.support, P.IsStrictTypeOne W ∨ P.IsStrictTypeTwo W ∨
      ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))))
    (t : ↥(modularFunctionFieldBar (1 * q))) (ht₁ : t ∈ R.R₁.integers) (ht₂ : t ∈ R.R₂.integers)
    (htord : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord t = E W)
    (n₁ n₂ : ℕ) (l₁ l₂ : k) (hl₁ : l₁ ≠ 0) (hl₂ : l₂ ≠ 0)
    (hn : ((n₁ : ℤ) + n₂) = Finsupp.mapDomain P.redFst E (frobNodePair q a).1)
    (htw₁ : (frobNodePair q a).1.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) a) ^ (-(n₁ : ℤ))
        * (R.residue₁ ⟨t, ht₁⟩ : ↥(modularFunctionFieldC k 1))) l₁)
    (htw₂ : (frobNodePair q a).2.HasValue
      (((⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) - algebraMap k ↥(modularFunctionFieldC k 1) (a ^ q)) ^ (-(n₂ : ℤ))
        * (R.residue₂ ⟨t, ht₂⟩ : ↥(modularFunctionFieldC k 1))) l₂) :
    R.SplitDatum S₀ E
      (Finsupp.mapDomain P.redFst (P.fstPart E) + Finsupp.single (frobNodePair q a).1 (n₁ : ℤ))
      (Finsupp.mapDomain P.redSnd (P.sndPart E) + Finsupp.single (frobNodePair q a).2 (n₂ : ℤ))
      (Function.update (fun _ => (1 : k)) a (l₂ * l₁⁻¹)) := by
  exact FltWs24.Asm.splitDatum_of_forall_centred_ord_eq_main R hR S₀ hS₀ hNR a ha ha2 E hE0 hEsupp t ht₁ ht₂
    htord n₁ n₂ l₁ l₂ hl₁ hl₂ hn htw₁ htw₂

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_splitDatum_of_forall_centred_ord_eq (solution)
