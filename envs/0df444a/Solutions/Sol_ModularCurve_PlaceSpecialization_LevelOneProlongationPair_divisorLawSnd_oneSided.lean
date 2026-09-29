-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.divisorLawSnd_oneSided
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/8cd75ab9-96f9-5f53-a31b-9941edc965f8

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawFst_oneSided
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_oneSided
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve IsLocalRing ModularCurve

namespace Ws14Fricke

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}

theorem redFst_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redFst (frickeInvolutionBar (1 * q) • W) = P.redSnd W := by
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul q hα hβ]

theorem redSnd_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redSnd (frickeInvolutionBar (1 * q) • W) = P.redFst W := by
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeBetaBar_frickeInvolutionBar_smul q hα hβ]

theorem isStrictTypeOne_frickeInvolutionBar_smul_iff (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeOne (frickeInvolutionBar (1 * q) • W) ↔ P.IsStrictTypeTwo W := by
  rw [PlaceSpecialization.IsStrictTypeOne, PlaceSpecialization.IsStrictTypeTwo,
    redFst_frickeInvolutionBar_smul P, redSnd_frickeInvolutionBar_smul P]
  exact and_congr eq_comm Iff.rfl

theorem mapDomain_redFst_filter_frickeInvolutionBar_smul (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    (letI := Classical.decPred P.IsStrictTypeOne; letI := Classical.decPred P.IsStrictTypeTwo;
    Finsupp.mapDomain P.redFst ((frickeInvolutionBar (1 * q) • D).filter P.IsStrictTypeOne)
      = Finsupp.mapDomain P.redSnd (D.filter P.IsStrictTypeTwo)) := by
  classical
  have hparts : (frickeInvolutionBar (1 * q) • D).filter P.IsStrictTypeOne
      = frickeInvolutionBar (1 * q) • D.filter P.IsStrictTypeTwo := by
    ext W
    rw [Divisor.smul_apply]
    simp only [Finsupp.filter_apply, Divisor.smul_apply]
    rw [← isStrictTypeOne_frickeInvolutionBar_smul_iff P, smul_inv_smul]
  rw [hparts, Divisor.smul_def, ← Finsupp.mapDomain_comp]
  congr 1
  funext W
  exact redFst_frickeInvolutionBar_smul P W

end Ws14Fricke

open Ws14Fricke in
open Classical in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : PlaceSpecialization.LevelOneProlongationPair P)
    (f : ↥(modularFunctionFieldBar (1 * q))) (h₂ : f ∈ R.R₂.integers) (hf : R.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hD : ∀ W, D W = W.ord f)
    (v : Place k ↥(modularFunctionFieldC k 1))
    (hv : frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) ≠ v) :
    Finsupp.mapDomain P.redSnd (D.filter P.IsStrictTypeTwo) v = v.ord (R.residue₂ ⟨f, h₂⟩) := by

  have hg₁ : (frickeInvolutionBar (1 * q)) f ∈ R.R₁.integers := (R.mem_integers₂_iff f).mp h₂
  have hres₁g : R.R₁.residue ⟨(frickeInvolutionBar (1 * q)) f, hg₁⟩ = R.R₂.residue ⟨f, h₂⟩ := (R.residue₂_eq f h₂).symm
  have hD' : ∀ W, ((frickeInvolutionBar (1 * q)) • D) W = W.ord ((frickeInvolutionBar (1 * q)) f) := fun W => by
    rw [AlgebraicCurve.Divisor.smul_apply, hD, ← Place.ord_smul (frickeInvolutionBar (1 * q)) ((frickeInvolutionBar (1 * q))⁻¹ • W), smul_inv_smul]
  have key := PlaceSpecialization.LevelOneProlongationPair.divisorLawFst_oneSided R ((frickeInvolutionBar (1 * q)) f) hg₁
    (hres₁g ▸ hf) ((frickeInvolutionBar (1 * q)) • D) hD' v hv
  rw [mapDomain_redFst_filter_frickeInvolutionBar_smul P D] at key
  rw [key, PlaceSpecialization.LevelOneProlongationPair.residue₁_apply, PlaceSpecialization.LevelOneProlongationPair.residue₂_apply, hres₁g]

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_oneSided
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_divisorLawSnd_oneSided (solution)
