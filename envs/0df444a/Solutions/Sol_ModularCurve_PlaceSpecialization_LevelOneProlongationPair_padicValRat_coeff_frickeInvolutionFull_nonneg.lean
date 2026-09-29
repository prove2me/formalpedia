-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.padicValRat_coeff_frickeInvolutionFull_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/2ae52346-c869-5431-8b83-892605b44208

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeff_mem_of_mem_integersFst_of_forall_ord_neg
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Theorems.Thm_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_jq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_padicValRat_coeff_frickeInvolutionFull_nonneg
p2m_attr_erase "instance" "ModularCurve.numberField_of_finiteDimensional ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.symPoly_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar"
p2m_attr_erase "simp" "AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option Elab.async false

open AlgebraicCurve ModularCurve IsLocalRing

noncomputable section

open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} [IsAlgClosed k] (R : P.LevelOneProlongationPair)
    (g : ↥(modularFunctionFieldFull (1 * q)))
    (hg : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W ≠ cuspInftyBar (1 * q) →
      0 ≤ W.ord (⟨coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) g.2⟩ : ↥(modularFunctionFieldBar (1 * q))))
    (hint : ∀ m : ℤ, 0 ≤ padicValRat q ((g : LaurentSeries ℚ).coeff m)) (m : ℤ) :
    0 ≤ padicValRat q (((frickeInvolutionFull (1 * q) g : ↥(modularFunctionFieldFull (1 * q))) :
      LaurentSeries ℚ).coeff m) := by
  classical
  have hp : q.Prime := Fact.out

  have hA : A.LiesOverPrime q := by
    have hqA : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
    show ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits
    rw [show ((q : ℕ) : AlgebraicClosure ℚ) = ((⟨_, hqA⟩ : A) : AlgebraicClosure ℚ) from rfl,
      ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : red ⟨_, hqA⟩ = 0 := by
      have : (⟨_, hqA⟩ : A) = ((q : ℕ) : A) := Subtype.ext (by simp)
      rw [this, map_natCast, CharP.cast_eq_zero]
    exact (hu.map red).ne_zero h1
  have hAq : A.valuation ((q : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff _).mp hA

  have hbridge : ∀ r : ℚ, (0 ≤ padicValRat q r ↔ ((r : ℚ) : AlgebraicClosure ℚ) ∈ A) := by
    intro r
    by_cases hr : r = 0
    · subst hr; simp
    · exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAq hr).symm

  set f : ↥(modularFunctionFieldBar (1 * q)) := ⟨coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) g.2⟩ with hfdef
  have hcoef : ∀ (x : ↥(modularFunctionFieldFull (1 * q))) (j : ℤ),
      (coeffEmb (AlgebraicClosure ℚ) (x : LaurentSeries ℚ)).coeff j
        = ((((x : LaurentSeries ℚ).coeff j : ℚ)) : AlgebraicClosure ℚ) := fun x j => by
    rw [coeffEmb_coeff, eq_ratCast]
  have hfA : ∀ j : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff j ∈ A := fun j => by
    show (coeffEmb (AlgebraicClosure ℚ) (g : LaurentSeries ℚ)).coeff j ∈ A
    rw [hcoef]
    exact (hbridge _).mp (hint j)

  let y : LaurentSeries A :=
    { coeff := fun j => ⟨(f : LaurentSeries (AlgebraicClosure ℚ)).coeff j, hfA j⟩
      isPWO_support' := (f : LaurentSeries (AlgebraicClosure ℚ)).isPWO_support.mono
        (fun _ hn h => hn (Subtype.ext h)) }
  have hy : coeffMap A.subtype y = (f : LaurentSeries (AlgebraicClosure ℚ)) := by
    ext j
    rfl
  have hyF : coeffMap A.subtype y ∈ modularFunctionFieldBar (1 * q) := by
    rw [hy]; exact SetLike.coe_mem _
  obtain ⟨hint₁, -⟩ := R.residue₁_coeffMap y hyF
  have hf₁ : f ∈ R.R₁.integers := by
    have helt : (⟨coeffMap A.subtype y, hyF⟩ : ↥(modularFunctionFieldBar (1 * q))) = f := Subtype.ext hy
    rw [← helt]; exact hint₁

  have hf₂ : f ∈ R.R₂.integers := mem_integersSnd_of_mem_integersFst_of_forall_ord_nonneg R f hg hf₁
  have hw₁ : frickeInvolutionBar (1 * q) f ∈ R.R₁.integers := (R.mem_integers₂_iff f).mp hf₂

  have hwf : frickeInvolutionBar (1 * q) f = ⟨coeffEmb (AlgebraicClosure ℚ)
      ((frickeInvolutionFull (1 * q) g : ↥(modularFunctionFieldFull (1 * q))) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (frickeInvolutionFull (1 * q) g).2⟩ :=
    geomAut_coeffEmb (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)) (frickeInvolutionFull (1 * q)) g

  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact hp⟩
  have hFr : IsFrickeAutFull (1 * q) (frickeInvolutionFull (1 * q)) :=
    ModularCurve.isFrickeAutFull_frickeInvolutionFull_prime (1 * q)
  have hj0 : (cuspZeroBar (1 * q)).ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩
        : ↥(modularFunctionFieldBar (1 * q))) < 0 := by
    have h := ModularCurve.ord_cuspZeroBar_coeffEmb_jq (1 * q) hFr
    have h' : (cuspZeroBar (1 * q)).ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩
        : ↥(modularFunctionFieldBar (1 * q))) = -((1 * q : ℕ) : ℤ) := h
    rw [h']
    have : 0 < q := hp.pos
    omega
  have hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)),
      W.ord (frickeInvolutionBar (1 * q) f) < 0 →
      W.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : ↥(modularFunctionFieldBar (1 * q))) < 0 := by
    intro W hW
    set w := frickeInvolutionBar (1 * q) with hw
    have htr := Place.ord_smul w (w⁻¹ • W) f
    rw [smul_inv_smul] at htr
    rw [htr] at hW
    have hWinf : w⁻¹ • W = cuspInftyBar (1 * q) := by
      by_contra hne
      exact absurd (hg _ hne) (not_le.mpr hW)
    have hW0 : W = cuspZeroBar (1 * q) := by
      rw [cuspZeroBar_def, ← hw, ← hWinf, smul_inv_smul]
    rw [hW0]
    exact hj0

  have hmem := coeff_mem_of_mem_integersFst_of_forall_ord_neg R (frickeInvolutionBar (1 * q) f) hpoles hw₁ m
  rw [hwf] at hmem
  change (coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull (1 * q) g : ↥(modularFunctionFieldFull (1 * q))) :
    LaurentSeries ℚ)).coeff m ∈ A at hmem
  rw [hcoef] at hmem
  exact (hbridge _).mpr hmem

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_padicValRat_coeff_frickeInvolutionFull_nonneg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_padicValRat_coeff_frickeInvolutionFull_nonneg (solution)
