-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a3bea35d-b3ab-580e-b5b8-9c86b0792d85

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
import Theorems.Thm_ModularCurve_PlaceSpecialization_reduceFst_atkinLehnerBar_smul
import Theorems.Thm_ModularCurve_PlaceSpecialization_isStrictFst_atkinLehnerBar_smul_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ}
    {R : P.ProlongationTuple} (hR : R.IsModel)
    {Q Q' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))}
    (hQ : P.IsStrictSnd Q) (hQ' : P.IsStrictSnd Q') (hQQ' : P.reduceSnd Q' = P.reduceSnd Q) (hne : Q' ≠ Q)
    (hQaff : IsAffineGeomPlace k 1 (P.reduceSnd Q))
    (a : k) (ha : (P.reduceSnd Q).evalAt (jGeomGen k 1) = a) (h0 : a ≠ 0) (h1728 : a ≠ 1728)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg₂ : g ∈ R.R₂.integers) (hg₂' : R.R₂.residue ⟨g, hg₂⟩ ≠ 0)
    (hgQ : Q.ord g = -(n : ℤ)) (hgQ' : Q'.ord g = n)
    (hg0 : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictSnd W → P.reduceSnd W = P.reduceSnd Q → W ≠ Q → W ≠ Q' → W.ord g = 0)
    (e : A) (ε : ↥(modularFunctionFieldBar (1 * q))) (hε₂ : ε ∈ R.R₂.integers) (hε₂' : R.R₂.residue ⟨ε, hε₂⟩ ≠ 0)
    (hgε : g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * ε) :
    -1 ≤ (P.reduceSnd Q).ord (R.residue₂ ⟨ε, hε₂⟩)  := by
  have hqN : ¬ q ∣ 1 := fun h => (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp h)
  set w : ↥(modularFunctionFieldBar (1 * q)) ≃ₐ[AlgebraicClosure ℚ] ↥(modularFunctionFieldBar (1 * q)) :=
    ProlongationTuple.atkinLehnerBar 1 q with hw

  have hwQ : P.IsStrictFst (w • Q) := (isStrictFst_atkinLehnerBar_smul_iff P hqN Q).mpr hQ
  have hwQ' : P.IsStrictFst (w • Q') := (isStrictFst_atkinLehnerBar_smul_iff P hqN Q').mpr hQ'
  have hred : ∀ W, P.reduceFst (w • W) = P.reduceSnd W := fun W => reduceFst_atkinLehnerBar_smul P hqN W
  have hwQQ' : P.reduceFst (w • Q') = P.reduceFst (w • Q) := by rw [hred, hred, hQQ']
  have hwne : w • Q' ≠ w • Q := fun h => hne (smul_left_cancel w h)
  have hwaff : IsAffineGeomPlace k 1 (P.reduceFst (w • Q)) := by rw [hred]; exact hQaff
  have hwa : (P.reduceFst (w • Q)).evalAt (jGeomGen k 1) = a := by rw [hred]; exact ha

  have hg₁ : w g ∈ R.R₁.integers := (R.mem_integers₂_iff g).mp hg₂
  have hε₁ : w ε ∈ R.R₁.integers := (R.mem_integers₂_iff ε).mp hε₂
  have hres_g : R.R₂.residue ⟨g, hg₂⟩ = R.R₁.residue ⟨w g, hg₁⟩ := R.residue₂_eq g hg₂
  have hres_ε : R.R₂.residue ⟨ε, hε₂⟩ = R.R₁.residue ⟨w ε, hε₁⟩ := R.residue₂_eq ε hε₂
  have hg₁' : R.R₁.residue ⟨w g, hg₁⟩ ≠ 0 := by rw [← hres_g]; exact hg₂'
  have hε₁' : R.R₁.residue ⟨w ε, hε₁⟩ ≠ 0 := by rw [← hres_ε]; exact hε₂'
  have hgwQ : (w • Q).ord (w g) = -(n : ℤ) := by rw [Place.ord_smul]; exact hgQ
  have hgwQ' : (w • Q').ord (w g) = n := by rw [Place.ord_smul]; exact hgQ'
  have hg0w : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      P.IsStrictFst W → P.reduceFst W = P.reduceFst (w • Q) → W ≠ w • Q → W ≠ w • Q' → W.ord (w g) = 0 := by
    intro W hW hWv h1 h2

    set W₀ := w⁻¹ • W with hW₀
    have hWW : w • W₀ = W := smul_inv_smul w W
    rw [← hWW] at hW hWv h1 h2 ⊢
    rw [Place.ord_smul]
    refine hg0 W₀ ((isStrictFst_atkinLehnerBar_smul_iff P hqN W₀).mp hW) ?_ (fun h => h1 (by rw [h]))
      (fun h => h2 (by rw [h]))
    rw [← hred, ← hred]; exact hWv
  have hgεw : w g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (e : AlgebraicClosure ℚ) * w ε := by
    rw [hgε, map_add, map_one, map_mul, AlgEquiv.commutes]

  have key := ModularCurve.PlaceSpecialization.ProlongationTuple.IsModel.neg_one_le_ord_residueFst_of_eq_one_add_mul_of_evalAt_ne_levelOne
    hR hwQ hwQ' hwQQ' hwne hwaff a hwa h0 h1728 n hn (w g) hg₁ hg₁' hgwQ hgwQ' hg0w e (w ε) hε₁ hε₁' hgεw

  have hres₂ : (R.residue₂ ⟨ε, hε₂⟩ : ↥(modularFunctionFieldC k 1)) = R.residue₁ ⟨w ε, hε₁⟩ := by
    rw [R.residue₂_apply, R.residue₁_apply, hres_ε]
  rw [hres₂, ← hred]
  exact key

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_IsModel_neg_one_le_ord_residueSnd_of_eq_one_add_mul_of_evalAt_ne_levelOne (solution)
