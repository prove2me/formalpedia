-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/30378abb-b621-5c07-b87b-3f9a71f25d0c

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersFst_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_exists_hasValue_and_hasValue_frobNodePair_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_exists_hasValue_frobNodePair_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_cuspLawInfty_oneSided
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_cuspInftyBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residue_fst_eq_zero_of_forall_ne
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_not_isInftySide_cuspZeroBar
import Theorems.Thm_ModularCurve_isZeroSide_cuspZeroBar
import Theorems.Thm_ModularCurve_isInftySide_cuspInftyBar
import Theorems.Thm_ModularCurve_not_isStrictType_of_isCuspidalSnd
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_ssJSet_nonempty
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg.ModularCurve IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral KroneckerCongruence frobNodePair_snd charLGeomPlaceOfPoint deg_charLGeomPlaceOfPoint CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar cuspZeroBar_def cuspInftyBar exists_hasValue_frobNodePair_of_forall_pole_not_centred isInftySide_cuspInftyBar hasPrincipalDivisors_modularFunctionFieldC_of_perfectField ssJSet_nonempty pow_q_sq_eq_self_of_mem_ssJSet frickeInvolutionBar_frickeInvolutionBar"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair IsInftySide"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom mem_integers₂_iff residue₂_eq R₂ ι R₁ mem_integersFst_iff_coe_mem_modularLocalized ord_residueFst_nonneg_of_forall_ne_cuspZeroBar"
namespace RegB
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve"

variable {q : ℕ} [Fact q.Prime] {k : Type*} [Field k]

theorem mapDomain_filter_apply_nonneg
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (p : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Prop) [DecidablePred p]
    (g : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → Place k ↥(modularFunctionFieldC k 1))
    (b : Place k ↥(modularFunctionFieldC k 1))
    (h : ∀ W, p W → g W = b → 0 ≤ D W) :
    0 ≤ Finsupp.mapDomain g (D.filter p) b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  apply Finset.sum_nonneg
  intro W _
  rw [Finsupp.single_apply]
  split_ifs with hWb
  · rw [Finsupp.filter_apply]
    split_ifs with hpW
    · exact h W hpW hWb
    · exact le_rfl
  · exact le_rfl

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair.RegB

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg.ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization.LevelOneProlongationPair.RegB in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} [IsAlgClosed k] (R : P.LevelOneProlongationPair)
    (G : ↥(modularFunctionFieldBar (1 * q)))
    (hG : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ≠ cuspInftyBar (1 * q) → 0 ≤ W.ord G)
    (h₁ : G ∈ R.R₁.integers) :
    G ∈ R.R₂.integers := by
  classical
  by_contra hG₂
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hG₂ (zero_mem _)
  obtain ⟨π, hh₂, hres₂⟩ := R.R₂.exists_smul_mem G hG0
  have hπ0 : π ≠ 0 := R.R₂.smul_const_ne_zero hh₂ hres₂

  have hπinv : π⁻¹ ∉ A := by
    intro hmem
    apply hG₂
    have hGeq : G = π⁻¹ • (π • G) := by rw [smul_smul, inv_mul_cancel₀ hπ0, one_smul]
    rw [hGeq, Algebra.smul_def]
    exact mul_mem ((R.R₂.algebraMap_mem_iff _).mpr hmem) hh₂
  have hπA : π ∈ A := (A.mem_or_inv_mem π).resolve_right hπinv
  have hπnu : π ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have hgt : 1 < A.valuation π⁻¹ :=
      not_le.mp (fun hle => hπinv ((A.valuation_le_one_iff _).mp hle))
    rw [map_inv₀] at hgt
    exact (one_lt_inv₀ ((Valuation.pos_iff _).mpr hπ0)).mp hgt
  have hπmax : (⟨π, hπA⟩ : A) ∈ IsLocalRing.maximalIdeal A := ValuationSubring.coe_mem_nonunits_iff.mp hπnu
  have hresπ : IsLocalRing.residue A ⟨π, hπA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hπmax

  have hh₁ : π • G ∈ R.R₁.integers := by
    rw [Algebra.smul_def]
    exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr hπA) h₁
  have hres₁ : R.R₁.residue ⟨π • G, hh₁⟩ = 0 := by
    have hprod : (⟨π • G, hh₁⟩ : R.R₁.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) _ ((⟨π, hπA⟩ : A) : AlgebraicClosure ℚ),
            (R.R₁.algebraMap_mem_iff _).mpr hπA⟩ * ⟨G, h₁⟩ := by
      apply Subtype.ext
      show π • G = algebraMap (AlgebraicClosure ℚ) _ π * G
      exact Algebra.smul_def π G
    rw [hprod, map_mul, R.R₁.residue_algebraMap ⟨π, hπA⟩, hresπ, map_zero, zero_mul]

  set w := frickeInvolutionBar (1 * q) with hw
  have hf'₁ : w (π • G) ∈ R.R₁.integers := (R.mem_integers₂_iff _).mp hh₂
  have hf'res : R.R₁.residue ⟨w (π • G), hf'₁⟩ ≠ 0 := by
    rw [← R.residue₂_eq _ hh₂]
    exact hres₂
  have hf'res' : R.residue₁ ⟨w (π • G), hf'₁⟩ ≠ 0 := by
    rw [residue₁_apply]
    exact (map_ne_zero R.ι).mpr hf'res
  have hf'₂ : w (π • G) ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hw, ModularCurve.frickeInvolutionBar_frickeInvolutionBar]
    exact hh₁
  have hf'poles : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      W ≠ cuspZeroBar (1 * q) → 0 ≤ W.ord (w (π • G)) := by
    intro W hW
    have hne : w⁻¹ • W ≠ cuspInftyBar (1 * q) := by
      intro h'
      apply hW
      rw [cuspZeroBar_def, ← hw, ← h', smul_inv_smul]
    have htr := Place.ord_smul w (w⁻¹ • W) (π • G)
    rw [smul_inv_smul] at htr
    have hπF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) π ≠ 0 :=
      (map_ne_zero _).mpr hπ0
    rw [htr, Algebra.smul_def, (w⁻¹ • W).ord_mul hπF hG0, Place.ord_algebraMap, zero_add]
    exact hG _ hne

  have hreg : ∀ v : Place k ↥(modularFunctionFieldC k 1), 0 ≤ v.ord (R.residue₁ ⟨w (π • G), hf'₁⟩) :=
    fun v => ord_residueFst_nonneg_of_forall_ne_cuspZeroBar R (w (π • G)) hf'₁ hf'res' hf'₂ hf'poles v

  obtain ⟨a, ha⟩ := ModularCurve.ssJSet_nonempty (q := q) (k := k)
  have ha2 : a ^ (q ^ 2) = a := ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q ha
  have hO₁ := (R.mem_integersFst_iff_coe_mem_modularLocalized _).mp hh₁
  have hO₂ := (R.mem_integersFst_iff_coe_mem_modularLocalized _).mp hf'₁
  obtain ⟨k₁, hdict₁⟩ := R.residue₁_eq_modularRedLocHom _ hO₁
  have h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hO₁⟩ ∈ modularFunctionFieldC k 1 := by
    rw [← hdict₁]; exact SetLike.coe_mem _
  obtain ⟨k₂, hdict₂⟩ := R.residue₁_eq_modularRedLocHom _ hO₂
  have h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hO₂⟩ ∈ modularFunctionFieldC k 1 := by
    rw [← hdict₂]; exact SetLike.coe_mem _
  have hInf : P.IsInftySide (cuspInftyBar (1 * q)) := ModularCurve.isInftySide_cuspInftyBar P
  obtain ⟨c, hc₁, hc₂⟩ :=
    ModularCurve.exists_hasValue_frobNodePair_of_forall_pole_not_centred red a ha ha2 (π • G) hO₁ h₁F hO₂ h₂F (by
      rintro W hW ⟨⟨x, -, hxord⟩, -⟩
      have hW0 : W = cuspInftyBar (1 * q) := by
        by_contra hne
        have hGW := hG W hne
        have hπF : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) π ≠ 0 :=
          (map_ne_zero _).mpr hπ0
        rw [Algebra.smul_def, W.ord_mul hπF hG0, Place.ord_algebraMap, zero_add] at hW
        exact absurd hGW (not_le.mpr hW)
      subst hW0
      exact absurd hxord (not_lt.mpr (hInf.1 x)))

  have hzero₁ : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = 0 := by
    apply Subtype.ext
    show CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hO₁⟩
      = ((0 : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
    rw [← hdict₁, hres₁, map_zero]
  rw [hzero₁] at hc₁
  have hc0 : c = 0 := by
    obtain ⟨-, h0⟩ := (Place.hasValue_iff_mem_and_eq_or_ord_sub_pos _ _ _).mp hc₁
    rcases h0 with h0 | h0
    · exact ((map_eq_zero_iff _ (algebraMap k ↥(modularFunctionFieldC k 1)).injective).mp h0.symm)
    · by_contra hc
      rw [zero_sub, ← map_neg, Place.ord_algebraMap] at h0
      exact lt_irrefl 0 h0

  set y : ↥(modularFunctionFieldC k 1) := R.residue₁ ⟨w (π • G), hf'₁⟩ with hy
  have hy0 : y ≠ 0 := hf'res'
  have hyeq : (⟨_, h₂F⟩ : ↥(modularFunctionFieldC k 1)) = y := by
    apply Subtype.ext
    rw [hy, residue₁_apply]
    exact hdict₂.symm
  rw [hyeq, hc0, frobNodePair_snd] at hc₂
  have hpos : 0 < (charLGeomPlaceOfPoint k (a ^ q)).ord y := by
    obtain ⟨-, h0⟩ := (Place.hasValue_iff_mem_and_eq_or_ord_sub_pos _ _ _).mp hc₂
    rcases h0 with h0 | h0
    · exact absurd (by rw [h0, map_zero]) hy0
    · simpa using h0

  haveI : HasPrincipalDivisors k ↥(modularFunctionFieldC k 1) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField k 1
  obtain ⟨E, hE, hEdeg⟩ := HasPrincipalDivisors.exists_divisor (K := k) y hy0
  have hEnn : ∀ v, 0 ≤ E v := fun v => by rw [hE]; exact hreg v
  set v₀ := charLGeomPlaceOfPoint k (a ^ q) with hv₀
  have hEv₀ : 0 < E v₀ := by rw [hE]; exact hpos
  have hdegv₀ : v₀.deg = 1 := deg_charLGeomPlaceOfPoint k (a ^ q)
  have hsum : Divisor.degree E = ∑ v ∈ E.support, E v * (v.deg : ℤ) := by
    show (Finsupp.liftAddHom fun v => AddMonoidHom.mulRight ((Place.deg v : ℕ) : ℤ)) E = _
    rw [Finsupp.liftAddHom_apply, Finsupp.sum]
    rfl
  have hmem : v₀ ∈ E.support := by
    rw [Finsupp.mem_support_iff]
    exact ne_of_gt hEv₀
  have hle : E v₀ * (v₀.deg : ℤ) ≤ ∑ v ∈ E.support, E v * (v.deg : ℤ) :=
    Finset.single_le_sum (fun v _ => mul_nonneg (hEnn v) (Int.natCast_nonneg _)) hmem
  rw [← hsum, hEdeg, hdegv₀] at hle
  push_cast at hle
  omega

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg (solution)
