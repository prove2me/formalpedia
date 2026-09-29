-- Prove2me | solution 1 for ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e09b8037-0761-5b4b-bda9-e5f681280fc3

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_NodeDescent
import Theorems.Thm_ModularCurve_isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar"
p2m_attr_erase "simp" "ModularCurve.coe_heckeAlphaBar ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of"
p2m_attr_erase "simp" "AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of"
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

noncomputable section

private theorem frac_close
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → 0 ≤ W.ord f)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (hInt : IsIntegral
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
      (f : LaurentSeries (AlgebraicClosure ℚ)))
    (hIC : IsIntegrallyClosed
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (y z : LaurentSeries (AlgebraicClosure ℚ))
    (hy : y ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hz : z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hz0 : z ≠ 0) (hfz : (f : LaurentSeries (AlgebraicClosure ℚ)) * z = y) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  have _ := h₂
  have _ := hq; have _ := ha; have _ := ha2; have _ := hford; have _ := hx; have _ := h₁; have _ := hfK
  set R₀K := modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)
  haveI hRdom : IsDomain ↥R₀K := Subring.instIsDomainSubtypeMem _
  have hginj : Function.Injective R₀K.subtype := Subtype.val_injective
  let ψ : FractionRing ↥R₀K →+* LaurentSeries (AlgebraicClosure ℚ) := IsFractionRing.lift hginj
  have hψinj : Function.Injective ψ := RingHom.injective ψ
  have hψalg : ∀ r : ↥R₀K,
      ψ (algebraMap ↥R₀K (FractionRing ↥R₀K) r) = R₀K.subtype r := fun r => by
    show IsFractionRing.lift hginj (algebraMap ↥R₀K (FractionRing ↥R₀K) r) = R₀K.subtype r
    exact IsFractionRing.lift_algebraMap (K := FractionRing ↥R₀K) hginj r
  have hzR : (⟨z, hz⟩ : ↥R₀K) ≠ 0 := fun h => hz0 (congrArg Subtype.val h)
  let f₀ : FractionRing ↥R₀K :=
    IsLocalization.mk' _ (⟨y, hy⟩ : ↥R₀K) ⟨⟨z, hz⟩, mem_nonZeroDivisors_of_ne_zero hzR⟩
  have hψf₀ : ψ f₀ = (f : LaurentSeries (AlgebraicClosure ℚ)) := by
    have hspec := IsLocalization.mk'_spec (FractionRing ↥R₀K)
      (⟨y, hy⟩ : ↥R₀K) ⟨⟨z, hz⟩, mem_nonZeroDivisors_of_ne_zero hzR⟩
    have hψspec := congrArg ψ hspec
    rw [map_mul, hψalg, hψalg] at hψspec
    have : ψ f₀ * z = y := hψspec
    have hfz' : (f : LaurentSeries (AlgebraicClosure ℚ)) * z = y := hfz
    have := this.trans hfz'.symm
    exact mul_right_cancel₀ hz0 this
  have hIntf₀ : IsIntegral ↥R₀K f₀ := by
    obtain ⟨P, hPm, hPf⟩ := hInt
    refine ⟨P, hPm, ?_⟩
    apply hψinj
    rw [map_zero, Polynomial.hom_eval₂, hψf₀]
    have hcomp : ψ.comp (algebraMap ↥R₀K (FractionRing ↥R₀K)) = R₀K.subtype :=
      RingHom.ext fun r => (RingHom.comp_apply _ _ _).trans (hψalg r)
    rw [hcomp]
    exact hPf
  obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥R₀K)).mp hIntf₀
  have heq : (f : LaurentSeries (AlgebraicClosure ℚ)) =
      R₀K.subtype r := by
    rw [← hψf₀, ← hr]; exact hψalg r
  rw [heq]; exact r.2

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → 0 ≤ W.ord f)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K) :
    (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by

  have hpole : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f < 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
                - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) := by
    intro W hWord hWc
    exact not_lt.mpr (hford W hWc) hWord

  have hInt := ModularCurve.isIntegral_modularLocalizedAtPoint_coeffSubring_of_forall_pole_not_centred
    red a K f hfK h₁ h₂ hpole

  have hIC : IsIntegrallyClosed
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) := by
    by_cases h0 : a = 0
    · exact ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
        red a ha ha2 hq (Or.inl h0) K ⟨x, hx⟩
    · by_cases h1728 : a = 1728
      · exact ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
          red a ha ha2 hq (Or.inr h1728) K ⟨x, hx⟩
      · exact ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
          red a ha ha2 hq h0 h1728 K ⟨x, hx⟩
  obtain ⟨y, z, hy, hz, hz0, hfz⟩ :=
    ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K hfK
  exact frac_close red hq a ha ha2 f h₁ h₂ hford K ⟨x, hx⟩ hfK hInt hIC y z hy hz hz0 hfz

#print axioms solution

end
end S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_redRestrict_eq_of_forall_centred_ord_nonneg (solution)
