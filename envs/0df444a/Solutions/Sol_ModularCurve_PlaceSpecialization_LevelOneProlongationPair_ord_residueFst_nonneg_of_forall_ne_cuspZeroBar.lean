-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d95b768b-250e-50a9-a5ee-ef249683ff62

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option Elab.async false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar.ModularCurve IsLocalRing"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar ModularPolynomialData modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel KroneckerCongruence frobNodePair_fst charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective CharPReduction.modularRedLocHom cuspZeroBar exists_hasValue_and_hasValue_frobNodePair_of_forall_pole_not_centred frobOnPlacesGeomLevel_charLGeomPlaceOfPoint not_isInftySide_cuspZeroBar isZeroSide_cuspZeroBar not_isStrictType_of_isCuspidalSnd hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair IsInftySide IsZeroSide IsStrictTypeOne redFst_cuspInftyBar"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom mem_integers₂_iff R₂ R₁ mem_integersFst_iff_coe_mem_modularLocalized divisorLawFst_oneSided cuspLawInfty_oneSided ord_residue_fst_eq_zero_of_forall_ne"
namespace RegA
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

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair.RegA

open _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar.ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization.LevelOneProlongationPair.RegA in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₁ : f ∈ R.R₁.integers) (hf : R.residue₁ ⟨f, h₁⟩ ≠ 0)
    (h₂ : f ∈ R.R₂.integers)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      W ≠ cuspZeroBar (1 * q) → 0 ≤ W.ord f)
    (v : Place k ↥(modularFunctionFieldC k 1)) :
    0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by
  classical
  haveI : DecidableEq (RatFunc k) := Classical.decEq _
  have hfR : R.R₁.residue ⟨f, h₁⟩ ≠ 0 := fun h0 => hf (by rw [residue₁_apply, h0, map_zero])
  have hg0 : R.residue₁ ⟨f, h₁⟩ ≠ 0 := hf
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hfR
    have : (⟨0, h₁⟩ : R.R₁.integers) = 0 := rfl
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) f hf0
  have hZ : P.IsZeroSide (cuspZeroBar (1 * q)) := ModularCurve.isZeroSide_cuspZeroBar P
  have hnotST1 : ¬ P.IsStrictTypeOne (cuspZeroBar (1 * q)) :=
    (ModularCurve.not_isStrictType_of_isCuspidalSnd P _ hZ.1).1
  have hnotInf : ¬ P.IsInftySide (cuspZeroBar (1 * q)) := ModularCurve.not_isInftySide_cuspZeroBar P
  have hDnn : ∀ W, W ≠ cuspZeroBar (1 * q) → 0 ≤ D W := fun W hW => by rw [hD]; exact hpoles W hW
  by_cases hvpt : ∃ a : k, v = charLGeomPlaceOfPoint k a
  · obtain ⟨a, rfl⟩ := hvpt
    by_cases ha2 : a ^ (q ^ 2) = a
    ·
      have hO₁ := (R.mem_integersFst_iff_coe_mem_modularLocalized f).mp h₁
      have hO₂ := (R.mem_integersFst_iff_coe_mem_modularLocalized _).mp ((R.mem_integers₂_iff f).mp h₂)
      obtain ⟨h₁', hdict₁⟩ := R.residue₁_eq_modularRedLocHom f hO₁
      have h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hO₁⟩ ∈ modularFunctionFieldC k 1 := by
        rw [← hdict₁]; exact SetLike.coe_mem _
      obtain ⟨h₂', hdict₂⟩ := R.residue₁_eq_modularRedLocHom _ hO₂
      have h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hO₂⟩ ∈ modularFunctionFieldC k 1 := by
        rw [← hdict₂]; exact SetLike.coe_mem _
      obtain ⟨c₁, c₂, hc₁, -⟩ :=
        ModularCurve.exists_hasValue_and_hasValue_frobNodePair_of_forall_pole_not_centred red a ha2 f hO₁ h₁F
          hO₂ h₂F (by
            rintro W hW ⟨-, y, -, hyord⟩
            have hW0 : W = cuspZeroBar (1 * q) := by
              by_contra hne
              exact absurd (hpoles W hne) (not_le.mpr hW)
            subst hW0
            exact absurd hyord (not_lt.mpr (hZ.1 y)))
      have hgeq : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) = R.residue₁ ⟨f, h₁⟩ := by
        apply Subtype.ext
        rw [residue₁_apply]
        exact hdict₁.symm
      rw [frobNodePair_fst, hgeq] at hc₁
      obtain ⟨hmem, -⟩ := (Place.hasValue_iff_mem_and_eq_or_ord_sub_pos _ _ _).mp hc₁
      exact (Place.mem_iff_ord_nonneg _ hg0).mp hmem
    ·
      have hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a))
          ≠ charLGeomPlaceOfPoint k a := by
        rw [ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint,
          ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint]
        intro h
        apply ha2
        have hinj := charLGeomPlaceOfPoint_injective k h
        calc a ^ (q ^ 2) = (a ^ q) ^ q := by ring
          _ = a := hinj
      have hlaw := R.divisorLawFst_oneSided f h₁ hfR D hD (charLGeomPlaceOfPoint k a) hv
      rw [← hlaw]
      apply mapDomain_filter_apply_nonneg
      intro W hW _
      apply hDnn
      rintro rfl
      exact hnotST1 hW
  · by_cases hvinf : v = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k)
    · have hlaw := R.cuspLawInfty_oneSided f h₁ hfR D hD
      rw [P.redFst_cuspInftyBar] at hlaw
      rw [hvinf, ← hlaw]
      apply mapDomain_filter_apply_nonneg
      intro W hW _
      apply hDnn
      rintro rfl
      exact hnotInf hW
    · push_neg at hvpt
      rw [R.ord_residue_fst_eq_zero_of_forall_ne ⟨f, h₁⟩ v (fun a h => hvpt a h) hvinf]

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_ord_residueFst_nonneg_of_forall_ne_cuspZeroBar (solution)
