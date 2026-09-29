-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/27d3fca3-ac31-5477-989a-2aee359de9fe

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_WeierstrassCurve_RatPointHom
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries' ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange"
p2m_attr_erase "instance" "ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄"
p2m_attr_erase "simp" "compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero"
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

noncomputable section

namespace Ws23
namespace SEP

section PlaceHelpers
variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem hasValue_add {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g + g') (a + a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have hx : (⟨g + g', add_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [hx, map_add, hr, hr', map_add]

theorem hasValue_neg {g : F} {a : K} (h : v.HasValue g a) : v.HasValue (-g) (-a) := by
  obtain ⟨hg, hr⟩ := h
  refine ⟨neg_mem hg, ?_⟩
  have hx : (⟨-g, neg_mem hg⟩ : v.toValuationSubring) = -⟨g, hg⟩ := rfl
  rw [hx, map_neg, hr, map_neg]

theorem hasValue_sub {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasValue_add h (hasValue_neg h')

theorem ord_pos_of_hasValue_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  obtain ⟨hm, hr⟩ := h
  rw [map_zero] at hr
  exact GaussReduction.ord_pos_of_residue_eq_zero v hm hg hr

theorem ord_nonneg_of_mem {g : F} (hm : g ∈ v.toValuationSubring) : 0 ≤ v.ord g := by
  by_cases hg : g = 0
  · rw [hg, Place.ord_zero]
  · exact GaussReduction.ord_nonneg_of_mem_gen v hm hg

end PlaceHelpers

theorem mem_ssJSet_of_pow_mem {K : Type} [Field K] [DecidableEq K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {c : K} (h : c ^ p ∈ ssJSet p K) : c ∈ ssJSet p K := by
  rw [mem_ssJSet_iff] at h ⊢
  intro W _ hW Pt hPt
  have hj : (W.map (frobenius K p)).j = c ^ p := by rw [WeierstrassCurve.map_j, hW, frobenius_def]
  have hQ := h (W.map (frobenius K p)) hj (WeierstrassCurve.ratPointMap (frobenius K p) (W₀ := W) Pt)
    (by rw [← ratPointMap_nsmul, hPt, WeierstrassCurve.ratPointMap_zero])
  exact WeierstrassCurve.ratPointMap_injective (frobenius K p) (W₀ := W)
    (hQ.trans (WeierstrassCurve.ratPointMap_zero _).symm)

theorem ramificationIndexAlong_pos' {K E E' : Type*} [Field K] [Field E] [Field E'] [Algebra K E] [Algebra K E']
    (φ : E →ₐ[K] E') (hφ : φ.toRingHom.IsIntegral) (w : Place K E') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.ramificationIndex_pos (F := E) (w := w)

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ}

local notation "ℚ̄" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "F" => ↥(modularFunctionFieldBar (1 * q))

def U (q : ℕ) [Fact q.Prime] : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩

theorem coe_U : ((U q : F) : LaurentSeries ℚ̄) = coeffEmb ℚ̄ (modularUnitSeries (1 * q)) := rfl

theorem jFun_def' : (jFun (q := q) : F) = ⟨coeffEmb ℚ̄ jq,
    coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := rfl

theorem natCast_one_mul : ((1 * q : ℕ) : ℚ̄) = (q : ℚ̄) := by rw [Nat.one_mul]

scoped instance fact_one_mul_prime : Fact (1 * q).Prime := ⟨by rw [Nat.one_mul]; exact Fact.out⟩

theorem qpow_ne_zero : ((q : ℚ̄) ^ 12) ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)

theorem fricke_U : frickeInvolutionBar (1 * q) (U q) = algebraMap ℚ̄ F ((q : ℚ̄) ^ 12) * (U q)⁻¹ := by
  have h := frickeInvolutionBar_coeffEmb_modularUnitSeries (1 * q)
    (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))
  rw [natCast_one_mul, ← HahnSeries.C_mul_eq_smul] at h
  apply Subtype.ext
  rw [MulMemClass.coe_mul, IntermediateField.coe_inv]
  convert h using 2
  all_goals first
    | rfl
    | (show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) _ = _
       rw [algebraMap_laurentSeries_eq_single]; rfl)
    | (show _ = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) _
       rw [algebraMap_laurentSeries_eq_single]; rfl)
    | (ext n; simp [algebraMap_laurentSeries_eq_single, HahnSeries.C_apply])

theorem fricke_fricke_U : frickeInvolutionBar (1 * q) (frickeInvolutionBar (1 * q) (U q)) = U q := by
  rw [fricke_U, map_mul, AlgEquiv.commutes, map_inv₀, fricke_U, mul_inv, ← mul_assoc,
    ← map_inv₀, ← map_mul, mul_inv_cancel₀ qpow_ne_zero, map_one, inv_inv, one_mul (U q)]

section WithPair
variable (R : P.LevelOneProlongationPair)

theorem U_mem₁ : (U q : F) ∈ R.R₁.integers := (R.coeffEmb_modularUnitSeries_mem_integersFst).1
theorem res₁_U_ne : R.R₁.residue ⟨U q, U_mem₁ R⟩ ≠ 0 := R.residue_coeffEmb_modularUnitSeries_ne_zero _
theorem U_mem₂ : (U q : F) ∈ R.R₂.integers := (R.coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero).1
theorem res₂_U : R.R₂.residue ⟨U q, U_mem₂ R⟩ = 0 := (R.coeffEmb_modularUnitSeries_mem_integersSnd_residue_eq_zero).2

theorem U_ne_zero' (R : P.LevelOneProlongationPair) : (U q : F) ≠ 0 := by
  intro h
  apply res₁_U_ne R
  have : (⟨U q, U_mem₁ R⟩ : R.R₁.integers) = 0 := Subtype.ext h
  rw [this, map_zero]

theorem Ut_mem₁ : frickeInvolutionBar (1 * q) (U q) ∈ R.R₁.integers := (R.mem_integers₂_iff _).mp (U_mem₂ R)

theorem Ut_mem₂ : frickeInvolutionBar (1 * q) (U q) ∈ R.R₂.integers :=
  (R.mem_integers₂_iff _).mpr (by rw [fricke_fricke_U]; exact U_mem₁ R)

theorem res₁_Ut : R.R₁.residue ⟨frickeInvolutionBar (1 * q) (U q), Ut_mem₁ R⟩ = 0 := by
  rw [← res₂_U R, R.residue₂_eq]

theorem res₂_Ut : R.R₂.residue ⟨frickeInvolutionBar (1 * q) (U q), Ut_mem₂ R⟩ = R.R₁.residue ⟨U q, U_mem₁ R⟩ := by
  rw [R.residue₂_eq]
  congr 1
  exact Subtype.ext (fricke_fricke_U)

theorem red_eq_zero_iff (R : P.LevelOneProlongationPair) (c : A) : red c = 0 ↔ c ∈ maximalIdeal A := by
  rw [← R.redBar_residue, map_eq_zero_iff _ (R.redBar).injective, IsLocalRing.residue_eq_zero_iff]

theorem algebraMap_mem₁ (c : A) : algebraMap ℚ̄ F (c : ℚ̄) ∈ R.R₁.integers := (R.R₁.algebraMap_mem_iff _).mpr c.2
theorem algebraMap_mem₂ (c : A) : algebraMap ℚ̄ F (c : ℚ̄) ∈ R.R₂.integers := (R.R₂.algebraMap_mem_iff _).mpr c.2

theorem res₁_algebraMap (c : A) : R.R₁.residue ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₁ R c⟩ =
    algebraMap (ResidueField A) _ (IsLocalRing.residue A c) := R.R₁.residue_algebraMap c
theorem res₂_algebraMap (c : A) : R.R₂.residue ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₂ R c⟩ =
    algebraMap (ResidueField A) _ (IsLocalRing.residue A c) := R.R₂.residue_algebraMap c

theorem res₁_algebraMap_eq_zero {c : A} (hc : c ∈ maximalIdeal A) :
    R.R₁.residue ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₁ R c⟩ = 0 := by
  rw [res₁_algebraMap, (IsLocalRing.residue_eq_zero_iff c).mpr hc, map_zero]
theorem res₂_algebraMap_eq_zero {c : A} (hc : c ∈ maximalIdeal A) :
    R.R₂.residue ⟨algebraMap ℚ̄ F (c : ℚ̄), algebraMap_mem₂ R c⟩ = 0 := by
  rw [res₂_algebraMap, (IsLocalRing.residue_eq_zero_iff c).mpr hc, map_zero]

variable {R}

theorem false_of_zero_on_fibre [hpd : HasPrincipalDivisors ℚ̄ F]
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (hvc : v ≠ P.redFst (cuspInftyBar (1 * q)))
    (f : F) (hf : f ≠ 0) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (h₁' : R.R₁.residue ⟨f, h₁⟩ ≠ 0) (h₂' : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (hord : v.ord (R.residue₁ ⟨f, h₁⟩) + (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩) ≤ 0)
    (hreg : ∀ W : Place ℚ̄ F, P.redFst W = v → f ∈ W.toValuationSubring)
    (W₀ : Place ℚ̄ F) (hW₀ : P.redFst W₀ = v) (hzero : 0 < W₀.ord f) : False := by
  classical
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf
  have hO := R.orderLawFixed f h₁ h₂ h₁' h₂' D hD v hv hvc

  have hsum : Finsupp.mapDomain P.redFst D v = D.sum (fun W n => if P.redFst W = v then n else 0) := by
    rw [Finsupp.mapDomain, Finsupp.sum_apply]
    simp only [Finsupp.single_apply]
  have hnonneg : ∀ W ∈ D.support, 0 ≤ (fun W n => if P.redFst W = v then n else 0) W (D W) := by
    intro W _
    simp only
    split_ifs with h
    · rw [hD]; exact ord_nonneg_of_mem (hreg W h)
    · exact le_rfl
  have hW₀D : W₀ ∈ D.support := by
    rw [Finsupp.mem_support_iff, hD]; exact ne_of_gt hzero
  have hge : D W₀ ≤ D.sum (fun W n => if P.redFst W = v then n else 0) := by
    rw [Finsupp.sum]
    have := Finset.single_le_sum hnonneg hW₀D
    simp only [hW₀, if_true] at this
    exact this
  have : 0 < Finsupp.mapDomain P.redFst D v := by
    rw [hsum]; exact lt_of_lt_of_le (by rw [hD]; exact hzero) hge
  omega

end WithPair

private theorem _root_.AlgebraicCurve.Place.isRational_of_deg_eq_one' {L E : Type*} [Field L] [Field E]
    [Algebra L E] (v : Place L E) (h : v.deg = 1) : v.IsRational := by
  intro z
  unfold Place.deg at h
  have hbt : (⊥ : Subalgebra L v.ResidueField) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h
  have hz : z ∈ (⊥ : Subalgebra L v.ResidueField) := by rw [hbt]; exact Algebra.mem_top
  exact Algebra.mem_bot.mp hz

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.AlgebraicCurve.Place.isRational_of_deg_eq_one'" "AlgebraicCurve.Place.isRational_of_deg_eq_one'"
theorem isRational_F (W : Place ℚ̄ F) : W.IsRational :=
  W.isRational_of_deg_eq_one' (deg_eq_one_modularFunctionFieldBar (1 * q) W)

theorem jFun_mem_of_not_isCuspidal {W : Place ℚ̄ F} (h : ¬ P.IsCuspidal W) :
    (jFun (q := q) : F) ∈ W.toValuationSubring := by
  simp only [IsCuspidal, not_forall, not_le] at h
  obtain ⟨a, ha⟩ := h
  have hne : (jFun (q := q) : F) - algebraMap ℚ̄ F (a : ℚ̄) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have hm := GaussReduction.mem_of_ord_nonneg_gen W hne (le_of_lt ha)
  have := add_mem hm (W.algebraMap_mem' (a : ℚ̄))
  rwa [sub_add_cancel] at this

theorem U_mem_and_inv_mem {W : Place ℚ̄ F} (hj : (jFun (q := q) : F) ∈ W.toValuationSubring) :
    (U q : F) ∈ W.toValuationSubring ∧ (U q : F)⁻¹ ∈ W.toValuationSubring := by

  have key : ∀ (x : LaurentSeries ℚ) (hx : coeffEmb ℚ̄ x ∈ modularFunctionFieldBar (1 * q)),
      IsIntegral (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) x →
      (⟨coeffEmb ℚ̄ x, hx⟩ : F) ∈ W.toValuationSubring := by
    intro x hx hint

    have hsub : ∀ r : LaurentSeries ℚ, r ∈ Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) →
        ∃ hr : coeffEmb ℚ̄ r ∈ modularFunctionFieldBar (1 * q), (⟨coeffEmb ℚ̄ r, hr⟩ : F) ∈ W.toValuationSubring := by
      intro r hr
      refine Algebra.adjoin_induction (hx := hr) ?_ ?_ ?_ ?_
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ⟨_, by simpa [jFun_def'] using hj⟩
      · intro c
        have hcoe : coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap ℚ̄ (LaurentSeries ℚ̄) (algebraMap ℚ ℚ̄ c) := by
          rw [algebraMap_laurentSeries_eq_single ℚ c, coeffEmb, coeffMap_single, algebraMap_laurentSeries_eq_single]
        have hmem : coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) c) ∈ modularFunctionFieldBar (1 * q) := by
          rw [hcoe]; exact IntermediateField.algebraMap_mem _ _
        refine ⟨hmem, ?_⟩
        have : (⟨coeffEmb ℚ̄ (algebraMap ℚ (LaurentSeries ℚ) c), hmem⟩ : F) = algebraMap ℚ̄ F (algebraMap ℚ ℚ̄ c) :=
          Subtype.ext hcoe
        rw [this]; exact W.algebraMap_mem' _
      · rintro y z - - ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨by rw [map_add]; exact add_mem hy hz, ?_⟩
        have : (⟨coeffEmb ℚ̄ (y + z), by rw [map_add]; exact add_mem hy hz⟩ : F) = ⟨_, hy⟩ + ⟨_, hz⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [this]; exact add_mem hy' hz'
      · rintro y z - - ⟨hy, hy'⟩ ⟨hz, hz'⟩
        refine ⟨by rw [map_mul]; exact mul_mem hy hz, ?_⟩
        have : (⟨coeffEmb ℚ̄ (y * z), by rw [map_mul]; exact mul_mem hy hz⟩ : F) = ⟨_, hy⟩ * ⟨_, hz⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [this]; exact mul_mem hy' hz'

    obtain ⟨p, hp, hpx⟩ := hint
    let O := W.toValuationSubring

    let θ : Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) →+* O :=
      { toFun := fun r => ⟨⟨coeffEmb ℚ̄ r, (hsub r r.2).1⟩, (hsub r r.2).2⟩
        map_one' := by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ 1 = _; rw [map_one]; rfl
        map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ (a * b) = _; rw [map_mul]; rfl
        map_zero' := by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ 0 = _; rw [map_zero]; rfl
        map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; show coeffEmb ℚ̄ (a + b) = _; rw [map_add]; rfl }
    have hθ : ∀ r, ((θ r : O) : F) = ⟨coeffEmb ℚ̄ r, (hsub r r.2).1⟩ := fun r => rfl

    have hcompeq : (algebraMap F (LaurentSeries ℚ̄)).comp ((algebraMap O F).comp θ)
        = (coeffEmb ℚ̄).comp (algebraMap (Algebra.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ)) :=
      RingHom.ext (fun r => rfl)
    have hxF : IsIntegral O (⟨coeffEmb ℚ̄ x, hx⟩ : F) := by
      refine ⟨p.map θ, hp.map θ, ?_⟩
      rw [Polynomial.eval₂_map]
      apply (algebraMap F (LaurentSeries ℚ̄)).injective
      rw [map_zero, Polynomial.hom_eval₂, hcompeq,
        show algebraMap F (LaurentSeries ℚ̄) (⟨coeffEmb ℚ̄ x, hx⟩ : F) = coeffEmb ℚ̄ x from rfl,
        ← Polynomial.hom_eval₂, hpx, map_zero]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hxF
    rw [← hy]
    exact y.2
  constructor
  · exact key _ _ (isIntegral_adjoin_jq_modularUnitSeries (1 * q))
  · have hx : coeffEmb ℚ̄ (modularUnitSeries (1 * q))⁻¹ ∈ modularFunctionFieldBar (1 * q) := by
      rw [map_inv₀]; exact inv_mem (U q).2
    have h := key _ hx (isIntegral_adjoin_jq_modularUnitSeries_inv (1 * q))
    have : (⟨coeffEmb ℚ̄ (modularUnitSeries (1 * q))⁻¹, hx⟩ : F) = (U q)⁻¹ := by
      apply Subtype.ext; show coeffEmb ℚ̄ (modularUnitSeries (1 * q))⁻¹ = _
      rw [map_inv₀]; rfl
    rwa [this] at h

section Core
variable (R : P.LevelOneProlongationPair)

theorem value_mem_A [hpd : HasPrincipalDivisors ℚ̄ F]
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (hvc : v ≠ P.redFst (cuspInftyBar (1 * q)))
    (h : F) (h₁ : h ∈ R.R₁.integers) (h₂ : h ∈ R.R₂.integers)
    (hreg : ∀ W : Place ℚ̄ F, P.redFst W = v → h ∈ W.toValuationSubring)
    (W : Place ℚ̄ F) (hW : P.redFst W = v) {t : ℚ̄} (ht : W.HasValue h t) (ht0 : t ≠ 0) : t ∈ A := by
  classical
  by_contra hna
  have hia : t⁻¹ ∈ A := (A.mem_or_inv_mem t).resolve_left hna
  set c : A := ⟨t⁻¹, hia⟩ with hc
  have hcm : c ∈ maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hna
    obtain ⟨w, hw⟩ := hu
    have h1 : ((w : A) : ℚ̄) * (((w⁻¹ : Aˣ) : A) : ℚ̄) = 1 := by
      rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    rw [hw] at h1
    have h2 : (((w⁻¹ : Aˣ) : A) : ℚ̄) = t := by
      have h3 : (((w⁻¹ : Aˣ) : A) : ℚ̄) = ((c : A) : ℚ̄)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]; show ((t⁻¹ : ℚ̄))⁻¹ = t; rw [inv_inv]
    rw [← h2]; exact SetLike.coe_mem _
  set g : F := 1 - algebraMap ℚ̄ F (c : ℚ̄) * h with hg
  have hg₁ : g ∈ R.R₁.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem₁ R c) h₁)
  have hg₂ : g ∈ R.R₂.integers := sub_mem (one_mem _) (mul_mem (algebraMap_mem₂ R c) h₂)
  have hres₁ : R.R₁.residue ⟨g, hg₁⟩ = 1 := by
    have : (⟨g, hg₁⟩ : R.R₁.integers) = 1 - ⟨_, algebraMap_mem₁ R c⟩ * ⟨h, h₁⟩ := rfl
    rw [this, map_sub, map_one, map_mul, res₁_algebraMap_eq_zero R hcm, zero_mul, sub_zero]
  have hres₂ : R.R₂.residue ⟨g, hg₂⟩ = 1 := by
    have : (⟨g, hg₂⟩ : R.R₂.integers) = 1 - ⟨_, algebraMap_mem₂ R c⟩ * ⟨h, h₂⟩ := rfl
    rw [this, map_sub, map_one, map_mul, res₂_algebraMap_eq_zero R hcm, zero_mul, sub_zero]
  have hne₁ : R.R₁.residue ⟨g, hg₁⟩ ≠ 0 := by rw [hres₁]; exact one_ne_zero
  have hne₂ : R.R₂.residue ⟨g, hg₂⟩ ≠ 0 := by rw [hres₂]; exact one_ne_zero
  have hord : v.ord (R.residue₁ ⟨g, hg₁⟩) + (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨g, hg₂⟩) ≤ 0 := by
    rw [R.residue₁_apply, R.residue₂_apply, hres₁, hres₂, map_one, Place.ord_one, Place.ord_one, add_zero]
  have hgreg : ∀ W' : Place ℚ̄ F, P.redFst W' = v → g ∈ W'.toValuationSubring :=
    fun W' h' => sub_mem (one_mem _) (mul_mem (W'.algebraMap_mem' _) (hreg W' h'))
  have hgW : W.HasValue g 0 := by
    have := hasValue_sub W.hasValue_one ((W.hasValue_algebraMap (c : ℚ̄)).mul ht)
    rwa [show (c : ℚ̄) * t = 1 from inv_mul_cancel₀ ht0, sub_self] at this
  have hg0 : g ≠ 0 := by
    intro h0; apply hne₁
    have : (⟨g, hg₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  exact false_of_zero_on_fibre v hv hvc g hg0 hg₁ hg₂ hne₁ hne₂ hord hgreg W hW (ord_pos_of_hasValue_zero hgW hg0)

theorem core [hpd : HasPrincipalDivisors ℚ̄ F]
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (hvc : v ≠ P.redFst (cuspInftyBar (1 * q)))
    (hū₁ : v.ord (R.residue₁ ⟨U q, U_mem₁ R⟩) = 0)
    (hū₂ : (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₁ ⟨U q, U_mem₁ R⟩) = 0)
    (hfib : ∀ W : Place ℚ̄ F, P.redFst W = v → ¬ P.IsCuspidal W)
    (W : Place ℚ̄ F) (hW : P.redFst W = v) :
    ((∃ a : A, red a ≠ 0 ∧ W.HasValue (U q) (a : ℚ̄)) ∨
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) (U q)) (a : ℚ̄))) ∧
    ¬ ((∃ a : A, red a ≠ 0 ∧ W.HasValue (U q) (a : ℚ̄)) ∧
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) (U q)) (a : ℚ̄))) := by
  classical

  have hUW : ∀ W' : Place ℚ̄ F, P.redFst W' = v →
      (U q : F) ∈ W'.toValuationSubring ∧ (U q : F)⁻¹ ∈ W'.toValuationSubring :=
    fun W' h' => U_mem_and_inv_mem (jFun_mem_of_not_isCuspidal (hfib W' h'))
  have hUtW : ∀ W' : Place ℚ̄ F, P.redFst W' = v → frickeInvolutionBar (1 * q) (U q) ∈ W'.toValuationSubring := by
    intro W' h'
    rw [fricke_U]
    exact mul_mem (W'.algebraMap_mem' _) (hUW W' h').2

  obtain ⟨hUm, hUim⟩ := hUW W hW
  obtain ⟨a, ha, ha0'⟩ := W.exists_hasValue_of_surjective (isRational_F W) hUm
  have hUunit : IsUnit (⟨U q, hUm⟩ : W.toValuationSubring) :=
    ⟨⟨⟨U q, hUm⟩, ⟨(U q)⁻¹, hUim⟩, Subtype.ext (mul_inv_cancel₀ (U_ne_zero' R)),
      Subtype.ext (inv_mul_cancel₀ (U_ne_zero' R))⟩, rfl⟩
  have ha0 : a ≠ 0 := ha0' hUunit

  have hb : W.HasValue (frickeInvolutionBar (1 * q) (U q)) ((q : ℚ̄) ^ 12 * a⁻¹) := by
    rw [fricke_U]; exact (W.hasValue_algebraMap _).mul (ha.inv ha0)
  have hb0 : ((q : ℚ̄) ^ 12 * a⁻¹) ≠ 0 := mul_ne_zero qpow_ne_zero (inv_ne_zero ha0)

  have haA : a ∈ A := value_mem_A R v hv hvc (U q) (U_mem₁ R) (U_mem₂ R) (fun W' h' => (hUW W' h').1) W hW ha ha0
  have hbA : ((q : ℚ̄) ^ 12 * a⁻¹) ∈ A :=
    value_mem_A R v hv hvc _ (Ut_mem₁ R) (Ut_mem₂ R) hUtW W hW hb hb0

  have hq0 : red ((q : ℕ) : A) = 0 := by rw [map_natCast]; exact CharP.cast_eq_zero k q
  have hprod : (⟨a, haA⟩ : A) * ⟨_, hbA⟩ = ((q : ℕ) : A) ^ 12 := by
    apply Subtype.ext
    push_cast
    show a * ((q : ℚ̄) ^ 12 * a⁻¹) = (q : ℚ̄) ^ 12
    rw [mul_comm, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  refine ⟨?_, ?_⟩
  ·
    by_cases hra : red ⟨a, haA⟩ = 0
    · by_cases hrb : red ⟨_, hbA⟩ = 0
      ·
        exfalso
        have ham : (⟨a, haA⟩ : A) ∈ maximalIdeal A := (red_eq_zero_iff R _).mp hra
        have hbm : (⟨_, hbA⟩ : A) ∈ maximalIdeal A := (red_eq_zero_iff R _).mp hrb
        set s : A := ⟨a, haA⟩ + ⟨_, hbA⟩ with hs
        have hsm : s ∈ maximalIdeal A := add_mem ham hbm
        set f : F := U q + frickeInvolutionBar (1 * q) (U q) - algebraMap ℚ̄ F (s : ℚ̄) with hf
        have hf₁ : f ∈ R.R₁.integers := sub_mem (add_mem (U_mem₁ R) (Ut_mem₁ R)) (algebraMap_mem₁ R s)
        have hf₂ : f ∈ R.R₂.integers := sub_mem (add_mem (U_mem₂ R) (Ut_mem₂ R)) (algebraMap_mem₂ R s)
        have hres₁ : R.R₁.residue ⟨f, hf₁⟩ = R.R₁.residue ⟨U q, U_mem₁ R⟩ := by
          have : (⟨f, hf₁⟩ : R.R₁.integers) = ⟨U q, U_mem₁ R⟩ + ⟨_, Ut_mem₁ R⟩ - ⟨_, algebraMap_mem₁ R s⟩ := rfl
          rw [this, map_sub, map_add, res₁_Ut, res₁_algebraMap_eq_zero R hsm, add_zero, sub_zero]
        have hres₂ : R.R₂.residue ⟨f, hf₂⟩ = R.R₁.residue ⟨U q, U_mem₁ R⟩ := by
          have : (⟨f, hf₂⟩ : R.R₂.integers) = ⟨U q, U_mem₂ R⟩ + ⟨_, Ut_mem₂ R⟩ - ⟨_, algebraMap_mem₂ R s⟩ := rfl
          rw [this, map_sub, map_add, res₂_U, res₂_Ut, res₂_algebraMap_eq_zero R hsm, zero_add, sub_zero]
        have hne₁ : R.R₁.residue ⟨f, hf₁⟩ ≠ 0 := by rw [hres₁]; exact res₁_U_ne R
        have hne₂ : R.R₂.residue ⟨f, hf₂⟩ ≠ 0 := by rw [hres₂]; exact res₁_U_ne R
        have hord : v.ord (R.residue₁ ⟨f, hf₁⟩) + (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, hf₂⟩) ≤ 0 := by
          rw [R.residue₁_apply, R.residue₂_apply, hres₁, hres₂, ← R.residue₁_apply, hū₁, hū₂, add_zero]
        have hfreg : ∀ W' : Place ℚ̄ F, P.redFst W' = v → f ∈ W'.toValuationSubring :=
          fun W' h' => sub_mem (add_mem (hUW W' h').1 (hUtW W' h')) (W'.algebraMap_mem' _)
        have hfW : W.HasValue f 0 := by
          have := hasValue_sub (hasValue_add ha hb) (W.hasValue_algebraMap (s : ℚ̄))
          rwa [show (s : ℚ̄) = a + (q : ℚ̄) ^ 12 * a⁻¹ from rfl, sub_self] at this
        have hf0 : f ≠ 0 := by
          intro h0; apply hne₁
          have : (⟨f, hf₁⟩ : R.R₁.integers) = 0 := Subtype.ext h0
          rw [this, map_zero]
        exact false_of_zero_on_fibre v hv hvc f hf0 hf₁ hf₂ hne₁ hne₂ hord hfreg W hW (ord_pos_of_hasValue_zero hfW hf0)
      · exact Or.inr ⟨⟨_, hbA⟩, hrb, hb⟩
    · exact Or.inl ⟨⟨a, haA⟩, hra, ha⟩
  ·
    rintro ⟨⟨a', ha'0, ha'⟩, ⟨b', hb'0, hb'⟩⟩
    have e1 : (a' : ℚ̄) = a := ha'.unique ha
    have e2 : (b' : ℚ̄) = (q : ℚ̄) ^ 12 * a⁻¹ := hb'.unique hb
    have : a' * b' = ((q : ℕ) : A) ^ 12 := by
      rw [← hprod]; congr 1 <;> exact Subtype.ext (by assumption)
    have h := congrArg red this
    rw [map_mul, map_pow, hq0, zero_pow (by norm_num)] at h
    exact mul_ne_zero ha'0 hb'0 h

end Core

section Dictionary

variable (P)

theorem heckeAlphaBar_jOne :
    heckeAlphaBar ℚ̄ 1 q (⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
      modularFunctionFieldBar 1) = (jFun (q := q) : F) :=
  Subtype.ext (by rw [coe_heckeAlphaBar]; rfl)

theorem not_isAffineGeomPlace_reduceFst_of_isCuspidal {W : Place ℚ̄ F} (hW : P.IsCuspidal W) :
    ¬ IsAffineGeomPlace k 1 (P.reduceFst W) := by
  intro haff
  have hpole : (P.reduceFst W).ord (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) < 0 := by
    apply P.d0_j_pole (W.restrictAlong (heckeAlphaBar ℚ̄ 1 q) hα)
    intro a
    have h := hW a
    have e := Place.ord_restrictAlong (heckeAlphaBar ℚ̄ 1 q) hα W
      ((⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄ (modularFunctionField_le_full 1 (jq_mem 1))⟩ :
        modularFunctionFieldBar 1) - algebraMap ℚ̄ (modularFunctionFieldBar 1) (a : ℚ̄))
    rw [map_sub, AlgHom.commutes, heckeAlphaBar_jOne] at e
    have hepos := ramificationIndexAlong_pos' (heckeAlphaBar ℚ̄ 1 q) hα W
    by_contra hpos
    push_neg at hpos
    have : 0 < W.ord ((jFun (q := q) : F) - algebraMap ℚ̄ F (a : ℚ̄)) := by
      rw [e]; exact mul_pos (by exact_mod_cast hepos) hpos
    exact absurd h (not_le.mpr this)
  have hmem : (⟨jqModC k, jqModC_mem k 1⟩ : modularFunctionFieldC k 1) ∈ (P.reduceFst W).toValuationSubring := haff.1
  have := ord_nonneg_of_mem hmem
  omega

theorem not_isAffineGeomPlace_infty [DecidableEq (RatFunc k)] :
    ¬ IsAffineGeomPlace k 1 (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)) := by
  intro h
  have hmem : jGeomGen k 1 ∈ (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).toValuationSubring := h.1
  have hX : ratFuncEquivCharLOneC k (RatFunc.X : RatFunc k) = jGeomGen k 1 := by
    apply Subtype.ext
    show _ = jqModC k
    rw [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
    exact RatFunc.algEquivOfTranscendental_X (jqModC k) (transcendental_jqModC k)
  rw [charLGeomPlaceEquiv, Place.congrEquiv_apply, Place.congrRingEquiv_toValuationSubring,
    ValuationSubring.mem_comap] at hmem
  have hmem' : (RatFunc.X : RatFunc k) ∈ (RationalFunctionField.placeInfty k).toValuationSubring := by
    convert hmem using 1
    rw [← hX]
    exact ((ratFuncEquivCharLOneC k).toRingEquiv.symm_apply_apply _).symm
  rw [RationalFunctionField.placeInfty_toValuationSubring, Valuation.mem_valuationSubring_iff,
    RatFunc.inftyValuation.X] at hmem'
  exact absurd hmem' (not_le.mpr (by rw [← WithZero.exp_zero]; exact WithZero.exp_lt_exp.mpr zero_lt_one))

theorem ord_resU_eq_zero (R : P.LevelOneProlongationPair)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v)
    (haff : IsAffineGeomPlace k 1 v) (hord : v ∉ ssPlaces q 1 k) :
    v.ord (R.residue₁ ⟨U q, U_mem₁ R⟩) = 0 ∧
      (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₁ ⟨U q, U_mem₁ R⟩) = 0 := by
  classical

  have hUloc : ((U q : F) : LaurentSeries ℚ̄) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
    (R.mem_integersFst_iff_coe_mem_modularLocalized (U q)).mp (U_mem₁ R)
  obtain ⟨hU₁', hbridge⟩ := R.residue₁_eq_modularRedLocHom (U q) hUloc
  have hF : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hUloc⟩ ∈ modularFunctionFieldC k 1 := by
    rw [← hbridge]; exact SetLike.coe_mem _
  have hres_eq : R.residue₁ ⟨U q, U_mem₁ R⟩ = ⟨_, hF⟩ := Subtype.ext hbridge
  have h0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hUloc⟩ ≠ 0 := by
    intro hz
    apply res₁_U_ne R
    have : R.ι (R.R₁.residue ⟨U q, hU₁'⟩) = 0 := Subtype.ext (by rw [hbridge, hz]; rfl)
    exact (map_eq_zero_iff _ R.ι.injective).mp this

  have hsupp : ∀ (a : k) (W : Place ℚ̄ F), W.ord (U q : F) ≠ 0 →
      ¬ ((∃ x : A, red x = a ∧ 0 < W.ord ((⟨coeffEmb ℚ̄ jq, coeffEmb_mem_laurentBaseChange ℚ̄
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : F) - algebraMap ℚ̄ F (x : ℚ̄))) ∧
         (∃ y : A, red y = a ^ q ∧ 0 < W.ord ((⟨coeffEmb ℚ̄ (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange ℚ̄
            (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : F) - algebraMap ℚ̄ F (y : ℚ̄)))) := by
    rintro a W hW ⟨⟨x, -, hx⟩, -⟩
    apply hW
    have hj : (jFun (q := q) : F) ∈ W.toValuationSubring := by
      apply jFun_mem_of_not_isCuspidal (P := P)
      intro hc; exact absurd (hc x) (not_le.mpr hx)
    obtain ⟨hm, him⟩ := U_mem_and_inv_mem (q := q) hj
    have hu : IsUnit (⟨U q, hm⟩ : W.toValuationSubring) :=
      ⟨⟨⟨U q, hm⟩, ⟨(U q)⁻¹, him⟩, Subtype.ext (mul_inv_cancel₀ (U_ne_zero' R)),
        Subtype.ext (inv_mul_cancel₀ (U_ne_zero' R))⟩, rfl⟩
    have := W.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec] at this

  by_cases hrat : v.IsRational
  ·
    have hcen := exists_isCentreOf_of_isRational hrat haff
    set c₀ : k := v.evalAt (jGeomGen k 1) with hc₀
    have hvc : v = charLGeomPlaceOfPoint k c₀ := eq_charLGeomPlaceOfPoint_of_ord_pos hcen.1
    have hcss : c₀ ∉ ssJSet q k := by
      intro hss
      apply hord
      rw [mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq]
      exact ⟨c₀, hss, hvc.symm⟩
    have hcq : c₀ ^ q ∉ ssJSet q k := by
      intro hss
      apply hord
      rw [mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq]
      exact ⟨c₀, mem_ssJSet_of_pow_mem q hss, hvc.symm⟩
    refine ⟨?_, ?_⟩
    · rw [hres_eq, hvc]
      exact ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet red (U q) hUloc hF h0 _ hcss (hsupp _)
    · rw [hres_eq, hvc, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
      exact ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet red (U q) hUloc hF h0 _ hcq (hsupp _)
  ·
    have hne : ∀ a : k, v ≠ charLGeomPlaceOfPoint k a := by
      intro a h; apply hrat; rw [h]
      exact (charLGeomPlaceOfPoint k a).isRational_of_deg_eq_one' (deg_charLGeomPlaceOfPoint k a)
    have hne' : v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
      intro h; rw [h] at haff; exact not_isAffineGeomPlace_infty haff
    have hφne : ∀ a : k, frobOnPlacesGeomLevel k 1 data hKr v ≠ charLGeomPlaceOfPoint k a := by
      intro a h
      apply hne (a ^ q)
      rw [← hv, h, frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
    have hφne' : frobOnPlacesGeomLevel k 1 data hKr v ≠ charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) := by
      intro h
      have := isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr v haff
      rw [h] at this; exact not_isAffineGeomPlace_infty this
    exact ⟨R.ord_residue_fst_eq_zero_of_forall_ne ⟨U q, U_mem₁ R⟩ v hne hne',
      R.ord_residue_fst_eq_zero_of_forall_ne ⟨U q, U_mem₁ R⟩ _ hφne hφne'⟩

end Dictionary

theorem sep_card [hpd : HasPrincipalDivisors ℚ̄ F] (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place ℚ̄ F)
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst W)) (hord : P.reduceFst W ∉ ssPlaces q 1 k) :
    ((∃ a : A, red a ≠ 0 ∧ W.HasValue (U q) (a : ℚ̄)) ∨
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) (U q)) (a : ℚ̄))) ∧
    ¬ ((∃ a : A, red a ≠ 0 ∧ W.HasValue (U q) (a : ℚ̄)) ∧
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) (U q)) (a : ℚ̄))) := by
  classical
  obtain ⟨R, -⟩ := LevelOneProlongationPair.exists_isModel P
  have hvc : P.reduceFst W ≠ P.redFst (cuspInftyBar (1 * q)) := by
    intro h
    apply not_isAffineGeomPlace_reduceFst_of_isCuspidal P (isInftySide_cuspInftyBar P).1
    show IsAffineGeomPlace k 1 (P.redFst (cuspInftyBar (1 * q)))
    rw [← h]; exact haff
  have hfib : ∀ W' : Place ℚ̄ F, P.redFst W' = P.reduceFst W → ¬ P.IsCuspidal W' := by
    intro W' h hc
    exact not_isAffineGeomPlace_reduceFst_of_isCuspidal P hc (show IsAffineGeomPlace k 1 (P.redFst W') by rw [h]; exact haff)
  obtain ⟨hū₁, hū₂⟩ := ord_resU_eq_zero P R (P.reduceFst W) hfix haff hord
  exact core R (P.reduceFst W) hfix hvc hū₁ hū₂ hfib W rfl

end Ws23.SEP
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.Ws23.SEP"
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.Ws23"
end
p2m_reactivate "P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.Ws23 P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary.Ws23.SEP"

theorem Ws23.SEP.modularUnitSeries_level_eq {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) :
    modularUnitSeries M = modularUnitSeries K := by subst h; rfl

theorem solution
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k] [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hfix : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (P.reduceFst W)) = P.reduceFst W)
    (haff : IsAffineGeomPlace k 1 (P.reduceFst W)) (hord : P.reduceFst W ∉ ssPlaces q 1 k) :
    ((∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∨
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ))) ∧
    ¬ ((∃ a : A, red a ≠ 0 ∧ W.HasValue u (a : AlgebraicClosure ℚ)) ∧
      (∃ a : A, red a ≠ 0 ∧ W.HasValue (frickeInvolutionBar (1 * q) u) (a : AlgebraicClosure ℚ))) := by
  have hU : u = Ws23.SEP.U q := by
    apply Subtype.ext
    rw [hu, Ws23.SEP.coe_U, Ws23.SEP.modularUnitSeries_level_eq (Nat.one_mul q)]
  subst hU
  exact Ws23.SEP.sep_card P W hfix haff hord

end S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_hasValue_modularUnit_or_frickeInvolutionBar_of_reduceFst_fixed_ordinary (solution)
