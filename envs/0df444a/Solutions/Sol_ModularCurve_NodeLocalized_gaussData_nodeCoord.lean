-- Prove2me | solution 1 for ModularCurve.NodeLocalized.gaussData_nodeCoord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7f155f7d-08dc-5f91-adb5-a58995d47a6e

import Mathlib
import Theorems.Thm_ModularCurve_modularEval_kroneckerRemainder
import Theorems.Thm_ModularCurve_eval_kroneckerRemainder_ne_zero_of_mem_ssJSet
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_kroneckerCongruence
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_StandardAnnulus
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_gaussData_nodeCoord
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_NodeLocalized_gaussData_nodeCoord.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_NodeLocalized_gaussData_nodeCoord.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "modularEval_kroneckerRemainder CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full transcendental_jqModC ssJSet frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace CharPReduction
p2m_export "ModularCurve.CharPReduction" "coeffRed_coeff redRes redRes_apply redKer notMem_redKer_iff mem_localizedAtKer subring_le_localizedAtKer redLoc redRes_ne_zero_of_notMem redLoc_spec redLoc_coe constSeries modularRing jqModC_mem_modularRing jqNModC_mem_modularRing constSeries_mem_modularRing jqModC_mem_integralCoeffs modularRing_le_integralCoeffs modularLocalized modularRedLocHom"
p2m_open "ModularCurve.CharPReduction ModularCurve"

variable (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L) {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_congr {x y : LaurentSeries L} (hxy : x = y)
    (h : ∃ hx : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    ∃ hy : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, hy⟩ ≠ 0 := by
  subst hxy
  exact h

theorem gaussUnit_one :
    ∃ h : (1 : LaurentSeries L) ∈ modularLocalized N A red, modularRedLocHom N A red ⟨1, h⟩ ≠ 0 := by
  refine ⟨one_mem _, ?_⟩
  have h1 : (⟨1, one_mem _⟩ : modularLocalized N A red) = 1 := rfl
  rw [h1, map_one]
  exact one_ne_zero

theorem gaussUnit_mul {x y : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0)
    (hy : ∃ h : y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨y, h⟩ ≠ 0) :
    ∃ h : x * y ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x * y, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨hy, hy0⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have hxy : (⟨x * y, mul_mem hx hy⟩ : modularLocalized N A red) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [hxy, map_mul]
  exact mul_ne_zero hx0 hy0

theorem gaussUnit_inv {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) :
    ∃ h : x⁻¹ ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x⁻¹, h⟩ ≠ 0 := by
  obtain ⟨hx, hx0⟩ := hx
  obtain ⟨r, s, hs, hxs⟩ :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mp hx
  have hsne := redRes_ne_zero_of_notMem (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) hs
  have hspec := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ hxs
  have hx0' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x, hx⟩ ≠ 0 := hx0
  have hrne : redRes A red (modularRing N A) (modularRing_le_integralCoeffs N A) r ≠ 0 := by
    rw [← hspec]
    exact mul_ne_zero hx0' hsne
  have hr : r ∉ redKer A red (modularRing N A) (modularRing_le_integralCoeffs N A) :=
    (notMem_redKer_iff A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr hrne
  have hxne : x ≠ 0 := by
    intro hx0
    apply hrne
    have hr0 : r = 0 := by
      apply Subtype.ext
      rw [← hxs, hx0, zero_mul]
      rfl
    rw [hr0, map_zero]
  have hinv : x⁻¹ * r = s := by
    rw [← hxs, ← mul_assoc, inv_mul_cancel₀ hxne, one_mul]
  have hmem : x⁻¹ ∈ modularLocalized N A red :=
    (mem_localizedAtKer A red (modularRing N A) (modularRing_le_integralCoeffs N A)).mpr ⟨s, r, hr, hinv⟩
  refine ⟨hmem, ?_⟩
  have hspec' := redLoc_spec (A := A) (red := red) (R := modularRing N A)
    (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ hinv
  intro hzero
  apply hsne
  have hzero' : redLoc (A := A) (red := red) (R := modularRing N A)
      (hR := modularRing_le_integralCoeffs N A) ⟨x⁻¹, hmem⟩ = 0 := hzero
  rw [← hspec', hzero', zero_mul]

theorem gaussUnit_pow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℕ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact gaussUnit_one N A red
  | succ n ih =>
      rw [pow_succ]
      exact gaussUnit_mul N A red ih hx

theorem gaussUnit_zpow {x : LaurentSeries L}
    (hx : ∃ h : x ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x, h⟩ ≠ 0) (n : ℤ) :
    ∃ h : x ^ n ∈ modularLocalized N A red, modularRedLocHom N A red ⟨x ^ n, h⟩ ≠ 0 := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast]
      exact gaussUnit_pow N A red hx n
  | negSucc n =>
      rw [zpow_negSucc]
      exact gaussUnit_inv N A red (gaussUnit_pow N A red hx (n + 1))

end ModularCurve.CharPReduction

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext HasValue hasValue_one residueInv_algebraMap evalAt evalAt_of_mem"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {v : Place K F}

theorem evalAt_eq_of_hasValue' {g : F} {a : K} (h : v.HasValue g a) : v.evalAt g = a := by
  rw [v.evalAt_of_mem h.mem, h.residue_eq, v.residueInv_algebraMap]

theorem hasValue_pow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero]
      exact v.hasValue_one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul h

theorem hasValue_zpow_of_hasValue {g : F} {a : K} (h : v.HasValue g a) (ha : a ≠ 0) (n : ℤ) :
    v.HasValue (g ^ n) (a ^ n) := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast]
      exact hasValue_pow_of_hasValue h n
  | negSucc n =>
      rw [zpow_negSucc, zpow_negSucc]
      exact (hasValue_pow_of_hasValue h (n + 1)).inv (pow_ne_zero _ ha)

end AlgebraicCurve.Place

namespace ModularCurve
p2m_export "ModularCurve" "modularEval_kroneckerRemainder CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.subring_le_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.redLoc_coe CharPReduction.constSeries CharPReduction.modularRing CharPReduction.jqModC_mem_modularRing CharPReduction.jqNModC_mem_modularRing CharPReduction.constSeries_mem_modularRing CharPReduction.jqModC_mem_integralCoeffs CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat map_jqModC jqModC_eq_map_intCast qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply jq ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full transcendental_jqModC ssJSet frickeInvolutionBar IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull modularFunctionFieldBar eval_kroneckerRemainder_ne_zero_of_mem_ssJSet frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero qExpand_jqModC_eq_pow_unconditional kroneckerCongruence reduceModBivar reduceModBivar_X reduceModBivar_C_X KroneckerCongruence nonempty_modularPolynomialData"
namespace NodeLocalized
p2m_export "ModularCurve.NodeLocalized" "modularEval"
p2m_open "ModularCurve.NodeLocalized ModularCurve"

theorem correction_identity {K : Type*} [Field K] (a c q w : K) (m : ℤ) :
    a * (c⁻¹ * q ^ (-m))⁻¹ * w ^ (-m) = c * a * (q * w⁻¹) ^ m := by
  rw [mul_zpow, inv_zpow', mul_inv, inv_inv, zpow_neg q m, inv_inv]
  ring

theorem isFrickeAutFull_one_mul (q : ℕ) [Fact q.Prime] :
    IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q))

theorem frickeInvolutionBar_jElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) 1 (1 * q) (one_mul _)
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro (1 * q) (one_mul _)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq).symm)
  rw [hj, h]

theorem frickeInvolutionBar_jqElt (q : ℕ) [Fact q.Prime] :
    frickeInvolutionBar (1 * q)
        (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
          modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := by
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * q) (isFrickeAutFull_one_mul q) (1 * q) 1 (mul_one _)
  have hjq : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ :
        modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (jqd_mem_full (1 * q) (Dvd.intro 1 (mul_one _)))⟩ := Subtype.ext rfl
  have hj : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (jqd_mem_full (1 * q) (Dvd.intro_left (1 * q) (mul_one _)))⟩ : modularFunctionFieldBar (1 * q))
      = ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ :=
    Subtype.ext (congrArg (coeffEmb (AlgebraicClosure ℚ)) (qExpand_one_apply jq))
  rw [hjq, h, hj]

theorem qExpand_one_mul {K : Type*} [CommRing K] (q : ℕ) [NeZero q] (x : LaurentSeries K) :
    qExpand K (1 * q) x = qExpand K q x := by
  ext n
  by_cases h : (q : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have e : ((1 * q : ℕ) : ℤ) * m = (q : ℤ) * m := by rw [one_mul]
    rw [qExpand_coeff_mul]
    conv_lhs => rw [← e]
    rw [qExpand_coeff_mul]
  · have h' : ¬ ((1 * q : ℕ) : ℤ) ∣ n := by rwa [one_mul]
    rw [qExpand_coeff_of_not_dvd _ _ h', qExpand_coeff_of_not_dvd _ _ h]

theorem jqNModC_one_mul_eq_pow (K : Type*) [CommRing K] (q : ℕ) [Fact q.Prime] [CharP K q] :
    jqNModC K (1 * q) = jqModC K ^ q := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  rw [jqNModC, qExpand_one_mul, qExpand_jqModC_eq_pow_unconditional K]

theorem coeffEmb_jq : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
  rw [← jqModC_rat]
  exact map_jqModC (algebraMap ℚ (AlgebraicClosure ℚ))

theorem coeffEmb_qExpand_jq (N : ℕ) [NeZero N] :
    coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq) = jqNModC (AlgebraicClosure ℚ) N := by
  rw [jqNModC, ← coeffEmb_jq]
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [coeffEmb_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [coeffEmb_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem algebraMap_eq_single' {K : Type*} [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
    HahnSeries.ofPowerSeries_C]
  rfl

section Red

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem red_coeff_jqModC (n : ℤ) (h : (jqModC (AlgebraicClosure ℚ)).coeff n ∈ A.toSubring) :
    red ⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ = (jqModC k).coeff n := by
  have hz : (⟨(jqModC (AlgebraicClosure ℚ)).coeff n, h⟩ : ↥A.toSubring)
      = ((jqModC ℤ).coeff n : ↥A.toSubring) := by
    apply Subtype.ext
    show (jqModC (AlgebraicClosure ℚ)).coeff n = (((jqModC ℤ).coeff n : ↥A.toSubring) : AlgebraicClosure ℚ)
    rw [jqModC_eq_map_intCast (K := AlgebraicClosure ℚ), HahnSeries.map_coeff, eq_intCast, SubringClass.coe_intCast]
  rw [hz, map_intCast, jqModC_eq_map_intCast (K := k), HahnSeries.map_coeff, eq_intCast]

theorem redRes_jqModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqModC k := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  exact red_coeff_jqModC red n _

theorem redRes_jqNModC :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩
      = jqNModC k (1 * q) := by
  ext n
  rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff]
  show red ⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, _⟩ = (jqNModC k (1 * q)).coeff n
  by_cases h : ((1 * q : ℕ) : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    have hm : (jqModC (AlgebraicClosure ℚ)).coeff m ∈ A.toSubring := CharPReduction.jqModC_mem_integralCoeffs A.toSubring m
    have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff ((1 * q : ℕ) * m), CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring)
        = ⟨(jqModC (AlgebraicClosure ℚ)).coeff m, hm⟩ :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff _ = _; rw [jqNModC, qExpand_coeff_mul])
    rw [hx, red_coeff_jqModC red m hm, jqNModC, qExpand_coeff_mul]
  · have hx : (⟨(jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n, CharPReduction.modularRing_le_integralCoeffs
          (1 * q) A.toSubring (CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring) _⟩ : ↥A.toSubring) = 0 :=
      Subtype.ext (by show (jqNModC (AlgebraicClosure ℚ) (1 * q)).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ)
                      rw [jqNModC, qExpand_coeff_of_not_dvd _ _ h]; rfl)
    rw [hx, map_zero, jqNModC, qExpand_coeff_of_not_dvd _ _ h]

theorem modularEval_mem_modularRing (N : ℕ) [NeZero N] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    modularEval N A.toSubring P ∈ CharPReduction.modularRing N A.toSubring := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      rw [modularEval, MvPolynomial.eval₂Hom_C]
      exact CharPReduction.constSeries_mem_modularRing N A.toSubring c
  | add p r hp hr => rw [map_add]; exact add_mem hp hr
  | mul_X p i hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      rw [modularEval, MvPolynomial.eval₂Hom_X']
      revert i
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · exact CharPReduction.jqModC_mem_modularRing N A.toSubring
      · exact CharPReduction.jqNModC_mem_modularRing N A.toSubring

theorem redRes_modularEval [CharP k q] (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
        ⟨modularEval (1 * q) A.toSubring P, modularEval_mem_modularRing (1 * q) P⟩
      = Polynomial.aeval (jqModC k)
          (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P) := by

  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)).comp
      ((modularEval (1 * q) A.toSubring).codRestrict (CharPReduction.modularRing (1 * q) A.toSubring)
        (modularEval_mem_modularRing (1 * q)))
  let ψ : MvPolynomial (Fin 2) ↥A.toSubring →+* LaurentSeries k :=
    (Polynomial.aeval (jqModC k)).toRingHom.comp
      (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφψ : φ = ψ := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    ·
      have hC : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨CharPReduction.constSeries A.toSubring c, CharPReduction.constSeries_mem_modularRing (1 * q) _ c⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_C _ _ c)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.C c), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.C c))
      rw [hC, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C, algebraMap_eq_single' (red c)]
      ext n
      rw [CharPReduction.redRes_apply, CharPReduction.coeffRed_coeff, HahnSeries.coeff_single]
      show red ⟨(CharPReduction.constSeries A.toSubring c).coeff n, _⟩ = _
      have hcs : ∀ m : ℤ, (CharPReduction.constSeries A.toSubring c).coeff m = if m = 0 then (c : AlgebraicClosure ℚ) else 0 := by
        intro m
        show (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (c : AlgebraicClosure ℚ)).coeff m = _
        rw [algebraMap_eq_single', HahnSeries.coeff_single]
        split_ifs <;> rfl
      by_cases hn : n = 0
      · subst hn
        have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff 0, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) 0⟩ : ↥A.toSubring) = c :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff 0 = c; rw [hcs, if_pos rfl])
        rw [hx, if_pos rfl]
      · have hx : (⟨(CharPReduction.constSeries A.toSubring c).coeff n, CharPReduction.modularRing_le_integralCoeffs (1 * q)
            A.toSubring (CharPReduction.constSeries_mem_modularRing (1 * q) _ c) n⟩ : ↥A.toSubring) = 0 :=
          Subtype.ext (by show (CharPReduction.constSeries A.toSubring c).coeff n = ((0 : ↥A.toSubring) : AlgebraicClosure ℚ);
                          rw [hcs, if_neg hn]; rfl)
        rw [hx, map_zero, if_neg hn]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqModC (AlgebraicClosure ℚ), CharPReduction.jqModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 0)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 0))
      rw [hX, redRes_jqModC, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Polynomial.aeval_X]
    ·
      have hX : (⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), modularEval_mem_modularRing (1 * q) _⟩ :
            ↥(CharPReduction.modularRing (1 * q) A.toSubring))
          = ⟨jqNModC (AlgebraicClosure ℚ) (1 * q), CharPReduction.jqNModC_mem_modularRing (1 * q) A.toSubring⟩ :=
        Subtype.ext (MvPolynomial.eval₂Hom_X' _ _ 1)
      show CharPReduction.redRes A.toSubring red _ _ ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 1), _⟩
        = Polynomial.aeval (jqModC k) (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
            (MvPolynomial.X 1))
      rw [hX, redRes_jqNModC, jqNModC_one_mul_eq_pow, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero,
        map_pow, Polynomial.aeval_X]
  exact RingHom.congr_fun hφψ P

omit [Fact q.Prime] in

theorem eval_graphReduce (a : k) (P : MvPolynomial (Fin 2) ↥A.toSubring) :
    Polynomial.eval a (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q] P)
      = MvPolynomial.eval₂Hom red ![a, a ^ q] P := by
  let φ : MvPolynomial (Fin 2) ↥A.toSubring →+* k :=
    (Polynomial.evalRingHom a).comp (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q])
  have hφ : φ = MvPolynomial.eval₂Hom red ![a, a ^ q] := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c)) = _
      rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, Polynomial.eval_C]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 0)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_zero, Polynomial.eval_X]
    · show Polynomial.eval a (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X 1)) = _
      rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero, Polynomial.eval_pow, Polynomial.eval_X]
  exact RingHom.congr_fun hφ P

omit [Fact q.Prime] in

theorem eval₂Hom_kroneckerPolynomial (a : k) (R : Polynomial (Polynomial ℤ)) :
    MvPolynomial.eval₂Hom red ![a, a ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)
      = ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a := by
  set E : MvPolynomial (Fin 2) ↥A.toSubring →+* k := MvPolynomial.eval₂Hom red ![a, a ^ q] with hE
  set g : Polynomial ℤ →+* MvPolynomial (Fin 2) ↥A.toSubring :=
    Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0) with hg
  have h1 : E (Polynomial.eval₂ g (MvPolynomial.X 1) R) = R.eval₂ (E.comp g) (E (MvPolynomial.X 1)) :=
    Polynomial.hom_eval₂ R g E (MvPolynomial.X 1)
  have hEg : E.comp g = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply, hE,
        MvPolynomial.eval₂Hom_C, eq_intCast, map_intCast, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, eq_intCast]
    · rw [RingHom.comp_apply, hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, hE, MvPolynomial.eval₂Hom_X',
        Matrix.cons_val_zero, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hEX : E (MvPolynomial.X 1) = a ^ q := by
    rw [hE, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [h1, hEg, hEX]

  have h2 : ((R.map (Polynomial.mapRingHom (Int.castRingHom k))).eval (Polynomial.C (a ^ q))).eval a
      = R.eval₂ ((Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k))) (Polynomial.eval a (Polynomial.C (a ^ q))) := by
    rw [Polynomial.eval_map, ← Polynomial.coe_evalRingHom, Polynomial.hom_eval₂]
  have h3 : (Polynomial.evalRingHom a).comp (Polynomial.mapRingHom (Int.castRingHom k)) = Polynomial.eval₂RingHom (Int.castRingHom k) a := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, Polynomial.coe_evalRingHom, Polynomial.eval_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    · rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Polynomial.coe_evalRingHom, Polynomial.eval_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [h2, h3, Polynomial.eval_C]

end Red

theorem exists_kroneckerRemainder (q : ℕ) [Fact q.Prime] (data : ModularPolynomialData q) :
    ∃ R : Polynomial (Polynomial ℤ),
      data.Φ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
        + Polynomial.C (Polynomial.C (q : ℤ)) * R := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hKr : KroneckerCongruence q data := kroneckerCongruence q data
  have hdvd : Polynomial.C (Polynomial.C (q : ℤ)) ∣
      data.Φ - (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h := congrArg (fun S : Polynomial (Polynomial (ZMod q)) => (S.coeff n).coeff m) hKr
    have hprod : reduceModBivar q ((Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q))
        = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q) := by
      simp only [map_mul, map_sub, map_pow, reduceModBivar_X, reduceModBivar_C_X]
    rw [← hprod] at h
    simp only [reduceModBivar, Polynomial.coe_mapRingHom, Polynomial.coeff_map, eq_intCast] at h
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.coeff_sub, Polynomial.coeff_sub, Int.cast_sub, sub_eq_zero]
    exact h
  obtain ⟨R, hR⟩ := hdvd
  exact ⟨R, by rw [← hR]; ring⟩

section Gauss

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] (red : A →+* k)

theorem gaussUnit_of_mem_modularRing {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩ ≠ 0) :
    ∃ h : x ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨x, h⟩ ≠ 0 := by
  refine ⟨CharPReduction.subring_le_localizedAtKer A.toSubring red _ _ hx, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have h := CharPReduction.redLoc_coe (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨x, hx⟩
  intro h0
  apply hred
  rw [← h]
  exact h0

theorem gaussUnit_of_mem_modularRing_div {r s : LaurentSeries (AlgebraicClosure ℚ)}
    (hr : r ∈ CharPReduction.modularRing (1 * q) A.toSubring) (hs : s ∈ CharPReduction.modularRing (1 * q) A.toSubring)
    (hrred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r, hr⟩ ≠ 0)
    (hsred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
        (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨s, hs⟩ ≠ 0) :
    ∃ h : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
      CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨r * s⁻¹, h⟩ ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h0
    apply hsred
    have : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hnot : (⟨s, hs⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) ∉ CharPReduction.redKer A.toSubring red
      (CharPReduction.modularRing (1 * q) A.toSubring) (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mpr hsred
  have hpres : r * s⁻¹ * s = r := by rw [mul_assoc, inv_mul_cancel₀ hs0, mul_one]
  have hmem : r * s⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := ⟨⟨r, hr⟩, ⟨s, hs⟩, hnot, hpres⟩
  refine ⟨hmem, ?_⟩
  show CharPReduction.redLoc _ ≠ 0
  have hspec := CharPReduction.redLoc_spec (A := A.toSubring) (red := red) (R := CharPReduction.modularRing (1 * q) A.toSubring)
    (hR := CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨r * s⁻¹, hmem⟩ (r := ⟨r, hr⟩) (s := ⟨s, hs⟩) hpres
  exact left_ne_zero_of_mul (ne_of_eq_of_ne hspec hrred)

theorem gaussData_nodeCoord' [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    (∃ (h₁ : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q))⁻¹ :
            modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) ∧
      (∃ (h₂ : ((frickeInvolutionBar (1 * q) (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)) : modularFunctionFieldBar (1 * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

  obtain ⟨J, hJ⟩ : ∃ J : ↥(modularFunctionFieldBar (1 * q)), J = ⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ := ⟨_, rfl⟩
  obtain ⟨JQ, hJQ⟩ : ∃ JQ : ↥(modularFunctionFieldBar (1 * q)), JQ = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ := ⟨_, rfl⟩
  rw [← hJ, ← hJQ]
  have hJser : (J : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by rw [hJ]; exact coeffEmb_jq
  have hJQser : (JQ : LaurentSeries (AlgebraicClosure ℚ)) = jqNModC (AlgebraicClosure ℚ) (1 * q) := by
    rw [hJQ]; exact coeffEmb_qExpand_jq (1 * q)

  have hGser : ((JQ - J ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]
  have hHser : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q) := by
    rw [AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, hJser, hJQser]
    simp only [modularEval, map_sub, map_pow, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Matrix.cons_val_one,
      Matrix.cons_val_zero]

  have hHred : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring)
      ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ ≠ 0 := by
    rw [redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      intro h
      have hdeg := congrArg Polynomial.natDegree (sub_eq_zero.mp h)
      rw [Polynomial.natDegree_X, ← pow_mul, Polynomial.natDegree_X_pow] at hdeg
      have h25 : 25 ≤ q * q := Nat.mul_le_mul hq hq
      rw [← hdeg] at h25
      exact absurd h25 (by norm_num)
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩

  obtain ⟨data⟩ := nonempty_modularPolynomialData q
  obtain ⟨R, hR⟩ := exists_kroneckerRemainder q data
  have hRne := eval_kroneckerRemainder_ne_zero_of_mem_ssJSet hq data R hR a ha h0 h1728
  have hEval := modularEval_kroneckerRemainder A data R hR
  rw [← hJ, ← hJQ] at hEval

  obtain ⟨Rser, hRser⟩ : ∃ Rser : LaurentSeries (AlgebraicClosure ℚ), Rser = modularEval (1 * q) A.toSubring
      (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
        (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring) := ⟨_, rfl⟩
  rw [← hRser] at hEval
  have hRmem : Rser ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hRser]; exact modularEval_mem_modularRing (1 * q) _
  have hRred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨Rser, hRmem⟩ ≠ 0 := by
    have hx : (⟨Rser, hRmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = ⟨modularEval (1 * q) A.toSubring
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring), modularEval_mem_modularRing (1 * q) _⟩ := Subtype.ext hRser
    rw [hx, redRes_modularEval]
    intro hzero
    have hQ : (MvPolynomial.eval₂Hom (Polynomial.C.comp red) ![Polynomial.X, Polynomial.X ^ q]
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom ↥A.toSubring)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) ↥A.toSubring)) ≠ 0 := by
      intro h
      apply hRne
      rw [← eval₂Hom_kroneckerPolynomial red a R, ← eval_graphReduce red a, h, Polynomial.eval_zero]
    exact transcendental_jqModC k ⟨_, hQ, hzero⟩
  have hHmem : ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      ∈ CharPReduction.modularRing (1 * q) A.toSubring := by rw [hHser]; exact modularEval_mem_modularRing (1 * q) _
  have hHred' : CharPReduction.redRes A.toSubring red (CharPReduction.modularRing (1 * q) A.toSubring)
      (CharPReduction.modularRing_le_integralCoeffs (1 * q) A.toSubring) ⟨_, hHmem⟩ ≠ 0 := by
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring))
        = ⟨modularEval (1 * q) A.toSubring (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q), modularEval_mem_modularRing (1 * q) _⟩ :=
      Subtype.ext hHser
    rw [hx]; exact hHred
  have hH0 : (J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h
    apply hHred'
    have hx : (⟨_, hHmem⟩ : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) = 0 :=
      Subtype.ext (by
        show ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = ((0 : ↥(CharPReduction.modularRing (1 * q) A.toSubring)) : LaurentSeries (AlgebraicClosure ℚ))
        rw [h]; rfl)
    rw [hx, map_zero]
  have hq0 : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  constructor
  ·
    have hident : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
        = (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
            * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ := by
      have h : (J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
            * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (JQ - J ^ q)⁻¹
            * ((J - JQ ^ q) * (J - JQ ^ q)⁻¹) := by
        rw [mul_inv, inv_inv, mul_inv]; ring
      rw [h, mul_inv_cancel₀ hH0, mul_one]
    have hcoe : (((J - JQ ^ q) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ))⁻¹
            * ((JQ - J ^ q) * (J - JQ ^ q)))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
        = ((J - JQ ^ q : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) * Rser⁻¹ := by
      rw [MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul, IntermediateField.coe_inv, MulMemClass.coe_mul,
        hEval, AddSubgroupClass.coe_sub, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, map_natCast,
        map_natCast, show (((q : ℕ) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
          = (modularFunctionFieldBar (1 * q)).val (q : ↥(modularFunctionFieldBar (1 * q))) from rfl, map_natCast]
    refine CharPReduction.gaussUnit_congr (1 * q) A.toSubring red ((congrArg Subtype.val hident).trans hcoe).symm ?_
    exact gaussUnit_of_mem_modularRing_div red hHmem hRmem hHred' hRred'
  ·
    have hσJ : frickeInvolutionBar (1 * q) J = JQ := by rw [hJ, hJQ]; exact frickeInvolutionBar_jElt q
    have hσJQ : frickeInvolutionBar (1 * q) JQ = J := by rw [hJ, hJQ]; exact frickeInvolutionBar_jqElt q
    have hσG : frickeInvolutionBar (1 * q) (JQ - J ^ q) = J - JQ ^ q := by rw [map_sub, map_pow, hσJ, hσJQ]
    rw [hσG]
    exact gaussUnit_of_mem_modularRing red hHmem hHred'

end Gauss

theorem gaussUnit_corrected {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (c : AlgebraicClosure ℚ) (m : ℤ) (f G : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : ∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (h₂ : ∃ h : ((frickeInvolutionBar (1 * q)
          (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hG₁ : ∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹ : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0)
    (hG₂ : ∃ h : ((frickeInvolutionBar (1 * q) G : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red, CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) :
    (∃ h : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) ∧
    (∃ h : ((frickeInvolutionBar (1 * q) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m) : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red,
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h⟩ ≠ 0) := by
  have coe_zpow : ∀ (x : ↥(modularFunctionFieldBar (1 * q))) (n : ℤ), ((x ^ n : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) = (x : LaurentSeries (AlgebraicClosure ℚ)) ^ n := by
    intro x n
    cases n with
    | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, zpow_natCast, IntermediateField.coe_pow]
    | negSucc n => rw [zpow_negSucc, zpow_negSucc, IntermediateField.coe_inv, IntermediateField.coe_pow]
  constructor
  · rw [MulMemClass.coe_mul, coe_zpow]
    exact CharPReduction.gaussUnit_mul (1 * q) A.toSubring red h₁
      (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hG₁ m)
  · have hσ : frickeInvolutionBar (1 * q) (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) c * f
          * (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * G⁻¹) ^ m)
        = frickeInvolutionBar (1 * q)
            (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (c * (q : AlgebraicClosure ℚ) ^ m) * f)
          * (frickeInvolutionBar (1 * q) G) ^ (-m) := by
      simp only [map_mul, map_zpow₀, AlgEquiv.commutes, mul_zpow, inv_zpow']
      ring
    rw [hσ, MulMemClass.coe_mul, coe_zpow]
    exact CharPReduction.gaussUnit_mul (1 * q) A.toSubring red h₂
      (CharPReduction.gaussUnit_zpow (1 * q) A.toSubring red hG₂ (-m))

end ModularCurve.NodeLocalized

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_NodeLocalized_gaussData_nodeCoord.AlgebraicCurve IsLocalRing _root_.ModularCurve _root_.P2MW.S_ModularCurve_NodeLocalized_gaussData_nodeCoord.ModularCurve in
theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k)
    [CharP k q] [IsAlgClosed k] [DecidableEq k] (hq : 5 ≤ q) (a : k) (ha : a ∈ ssJSet q k)
    (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    (∃ (h₁ : ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (q : AlgebraicClosure ℚ) * (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q))⁻¹ :
            modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
          CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0) ∧
      (∃ (h₂ : ((frickeInvolutionBar (1 * q) (((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
          - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) ^ q)) : modularFunctionFieldBar (1 * q)) :
            LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red),
        CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0) :=
  ModularCurve.NodeLocalized.gaussData_nodeCoord' red hq a ha h0 h1728

end

end S_ModularCurve_NodeLocalized_gaussData_nodeCoord
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_gaussData_nodeCoord (solution)
