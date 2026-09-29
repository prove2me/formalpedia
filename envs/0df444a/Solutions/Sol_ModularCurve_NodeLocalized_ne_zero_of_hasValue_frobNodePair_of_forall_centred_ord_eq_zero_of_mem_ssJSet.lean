-- Prove2me | solution 1 for ModularCurve.NodeLocalized.ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero_of_mem_ssJSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/43944e2d-9ff5-5635-a164-67b9a57416e5

import Mathlib
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodes
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_three
import Theorems.Thm_ModularCurve_eq_zero_of_mem_ssJSet_two
import Theorems.Thm_ModularCurve_exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_exists_mul_eq_of_height_one_of_natCast_mem
import Theorems.Thm_ModularCurve_exists_place_centred_node_of_height_one_of_natCast_notMem
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728
import Theorems.Thm_ModularCurve_isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728
import Theorems.Thm_ModularCurve_jIntegralClosure_isNoetherian_and_isLocalization
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_NodeLocalized_exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_NodeLocalized_exists_heightOne_mem_of_mul_eq_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_NodeLocalized_exists_isPrime_mem_of_mul_eq_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_mem_jIntegralClosure_of_not_isUnit_frobNodePair
import Theorems.Thm_ModularCurve_NodeLocalized_exists_mul_eq_of_mem_fieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring
import Theorems.Thm_ModularCurve_NodeLocalized_jqModC_mem_jIntegralClosure_and_jqNModC_mem
import Theorems.Thm_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver
import Theorems.Thm_ModularCurve_NodeLocalized_mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver_of_ne_zero_of_ne_1728
import Theorems.Thm_ModularCurve_NodeLocalized_natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_NodeLocalized_ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero_of_mem_ssJSet
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instTopologicallyFGOfFiniteType"
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"
p2m_attr_erase "simp" "AdicCompletion.stabilizerToCompletionAut_of"
set_option autoImplicit false

namespace BdA

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.NodeLocalized~sub_C_eval_mem_span"

noncomputable section

private theorem modularEval_mem_fieldOver {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (t : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) t ∈ fieldOver (1 * q) K := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    exact Subfield.subset_closure
      (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), (Subring.mem_inf.mp c.2).2⟩, rfl⟩)
  | add p r hp hr =>
    rw [map_add]
    exact (fieldOver (1 * q) K).add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine (fieldOver (1 * q) K).mul_mem hp ?_
    simp only [modularEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    exact Subfield.subset_closure (Or.inr (by fin_cases i <;> simp))

private theorem constSeries_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ jIntegralClosure (1 * q) A K := by
  refine ⟨?_, ?_⟩
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) =
        CharPReduction.constSeries (coeffSubring A K) c := MvPolynomial.eval₂Hom_C _ _ c
    rw [← h]
    exact modularEval_mem_fieldOver A K (MvPolynomial.C c)
  · have hmem : CharPReduction.constSeries (coeffSubring A K) c ∈ jRing A K :=
      Subring.subset_closure (Or.inl ⟨c, rfl⟩)
    exact isIntegral_algebraMap (x := (⟨_, hmem⟩ : ↥(jRing A K)))

private theorem modularEval_mem_jIntegralClosure {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (t : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) =
        CharPReduction.constSeries (coeffSubring A K) c := MvPolynomial.eval₂Hom_C _ _ c
    rw [h]
    exact constSeries_mem_jIntegralClosure A K c
  | add p r hp hr =>
    rw [map_add]
    exact add_mem hp hr
  | mul_X p i hp =>
    rw [map_mul]
    refine mul_mem hp ?_
    have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X i) =
        ![jqModC (AlgebraicClosure ℚ), jqNModC (AlgebraicClosure ℚ) (1 * q)] i := MvPolynomial.eval₂Hom_X' _ _ i
    rw [h]
    fin_cases i
    · exact (ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem A K).1
    · exact (ModularCurve.NodeLocalized.jqModC_mem_jIntegralClosure_and_jqNModC_mem A K).2

theorem exists_mul_eq_mem_jIntegralClosure_wide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (hfR : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :
    ∃ (p s : ↥(jIntegralClosure (1 * q) A K))
      (s₀ : MvPolynomial (Fin 2) ↥(coeffSubring A K)),
      (s : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) s₀ ∧
      pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s₀ ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
        (p : LaurentSeries (AlgebraicClosure ℚ)) := by
  have _ := hker
  have _ := ha
  have _ := ha2
  have _ := h₁
  have _ := h₁F
  have _ := h₁u
  have _ := h₂
  have _ := h₂F
  have _ := h₂u
  have _ := hmem
  have _ := hnu
  have _ := hfK
  obtain ⟨r, s₀, hs₀, hfs⟩ := hfR
  exact ⟨⟨_, modularEval_mem_jIntegralClosure A K r⟩, ⟨_, modularEval_mem_jIntegralClosure A K s₀⟩, s₀, rfl, hs₀, hfs⟩

end

end BdA

namespace BdB

noncomputable section

private theorem ord_nonneg_of_mem_place {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private theorem ord_pos_of_residue_eq_zero_place {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (h : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0) : 0 < v.ord f := by
  have hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.residue_eq_zero_iff _).mp h
  have hlt' : v.adicValuation f < 1 := (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mp hm
  have hge := ord_nonneg_of_mem_place v hf
  rcases lt_or_eq_of_le hge with h' | h'
  · exact h'
  · exact absurd ((v.ord_eq_zero_iff_adicValuation_eq_one hf0).mp h'.symm) (ne_of_lt hlt')

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.NodeLocalized~sub_C_eval_mem_span"

private theorem inv_mem_modularLocalized_of_ne_zero (N : ℕ) [NeZero N] (A : Subring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (red : A →+* k) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularLocalized N A red)
    (hu : CharPReduction.modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    x⁻¹ ∈ CharPReduction.modularLocalized N A red := by
  obtain ⟨r, s, hs, hxs⟩ := id hx
  have hx0 : x ≠ 0 := fun h => hu (by
    rw [show (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) = 0 from Subtype.ext h, map_zero])
  have hloc : CharPReduction.redLoc (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) ≠ 0 := fun h0 =>
    hu (by rw [show CharPReduction.modularRedLocHom N A red ⟨x, hx⟩ = CharPReduction.redLoc ⟨x, hx⟩ from
      CharPReduction.redLocHom_apply _]; exact h0)
  have hspec := CharPReduction.redLoc_spec (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) hxs
  have hr : r ∉ CharPReduction.redKer A red (CharPReduction.modularRing N A)
      (CharPReduction.modularRing_le_integralCoeffs N A) := by
    rw [CharPReduction.notMem_redKer_iff] at hs ⊢
    rw [← hspec]
    exact mul_ne_zero hloc hs
  refine (CharPReduction.mem_localizedAtKer _ _ _ _).mpr ⟨s, r, hr, ?_⟩
  rw [← hxs, inv_mul_cancel_left₀ hx0]

private theorem mem_of_isIntegral_of_mul_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (c : LaurentSeries (AlgebraicClosure ℚ))
    (hInt : IsIntegral
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) c)
    (hIC : IsIntegrallyClosed
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)))
    (y z : LaurentSeries (AlgebraicClosure ℚ))
    (hy : y ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hz : z ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    (hz0 : z ≠ 0) (hfz : c * z = y) :
    c ∈ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
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
  have hψf₀ : ψ f₀ = c := by
    have hspec := IsLocalization.mk'_spec (FractionRing ↥R₀K)
      (⟨y, hy⟩ : ↥R₀K) ⟨⟨z, hz⟩, mem_nonZeroDivisors_of_ne_zero hzR⟩
    have hψspec := congrArg ψ hspec
    rw [map_mul, hψalg, hψalg] at hψspec
    have : ψ f₀ * z = y := hψspec
    have hfz' : c * z = y := hfz
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
  have heq : c =
      R₀K.subtype r := by
    rw [← hψf₀, ← hr]; exact hψalg r
  rw [heq]; exact r.2

private theorem jRing_le_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] (red : A →+* k) (a : k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    jRing A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  refine Subring.closure_le.mpr ?_
  rintro y (⟨c, rfl⟩ | rfl)
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.C c) = CharPReduction.constSeries (coeffSubring A K) c :=
      MvPolynomial.eval₂Hom_C _ _ c
    rw [← h]
    exact modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _
  · have h : modularEval (1 * q) (coeffSubring A K) (MvPolynomial.X 0) = jqModC (AlgebraicClosure ℚ) :=
      MvPolynomial.eval₂Hom_X' _ _ 0
    rw [← h]
    exact modularEval_mem_modularLocalizedAtPoint _ _ _ _ _ _

private theorem jIntegralClosure_le_modularLocalizedAtPoint
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728) (hq : 5 ≤ q)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a) :
    jIntegralClosure (1 * q) A K ≤ modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
  intro c hc
  obtain ⟨hcF, hcInt⟩ := hc
  have hIC : IsIntegrallyClosed
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
    ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_eq_zero_or_eq_1728 red a ha ha2 hq h01728 K
      ⟨x, hx⟩
  have hle := jRing_le_modularLocalizedAtPoint (q := q) red a K
  have hInt : IsIntegral
      ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) c := by
    obtain ⟨P, hPm, hPe⟩ := hcInt
    refine ⟨P.map (Subring.inclusion hle), hPm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
        (LaurentSeries (AlgebraicClosure ℚ))).comp (Subring.inclusion hle) =
        algebraMap ↥(jRing A K) (LaurentSeries (AlgebraicClosure ℚ)) := RingHom.ext fun _ => rfl
    rw [hcomp]
    exact hPe
  obtain ⟨y, z, hy, hz, hz0, hcz⟩ := ModularCurve.NodeLocalized.exists_mul_eq_of_mem_fieldOver red a K hcF
  exact mem_of_isIntegral_of_mul_eq red a K c hInt hIC y z hy hz hz0 hcz

private theorem sub_C_eval_mem_span {R S : Type*} [CommRing R] [CommRing S]
    (φ : MvPolynomial (Fin 2) R →+* S) (x₀ x₁ : R) (t : MvPolynomial (Fin 2) R) :
    φ t - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] t)) ∈
      Ideal.span {φ (MvPolynomial.X 0 - MvPolynomial.C x₀), φ (MvPolynomial.X 1 - MvPolynomial.C x₁)} := by
  induction t using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.eval_C, sub_self]
    exact Ideal.zero_mem _
  | add p r hp hr =>
    rw [MvPolynomial.eval_add, MvPolynomial.C_add, map_add, map_add]
    have h : φ p + φ r - (φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p)) +
        φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] r))) =
        (φ p - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p))) +
        (φ r - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] r))) := by ring
    rw [h]
    exact Ideal.add_mem _ hp hr
  | mul_X p n hp =>
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.C_mul, map_mul, map_mul]
    have h : φ p * φ (MvPolynomial.X n) -
        φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p)) * φ (MvPolynomial.C (![x₀, x₁] n)) =
        φ p * (φ (MvPolynomial.X n) - φ (MvPolynomial.C (![x₀, x₁] n))) +
        (φ p - φ (MvPolynomial.C (MvPolynomial.eval ![x₀, x₁] p))) * φ (MvPolynomial.C (![x₀, x₁] n)) := by ring
    rw [h]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_right _ _ hp)
    rw [← map_sub]
    fin_cases n
    · exact Ideal.subset_span (Or.inl rfl)
    · exact Ideal.subset_span (Or.inr rfl)

private theorem exists_mul_eq_one_of_redRestrict_ne_zero
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) :
    ∃ d : ↥(coeffSubring A K), c * d = 1 := by
  let cA : A := Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) c
  have hcA : cA ∉ IsLocalRing.maximalIdeal A := fun h => hc ((hker cA).mpr h)
  obtain ⟨b, hb⟩ := (IsLocalRing.notMem_maximalIdeal.mp hcA).exists_right_inv
  have hb' : (c : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hb'; exact zero_ne_one hb'
  have hbinv : (b : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
  have hbK : (b : AlgebraicClosure ℚ) ∈ K.toSubalgebra.toSubring := by
    rw [hbinv]
    exact K.inv_mem (Subring.mem_inf.mp c.2).2
  refine ⟨⟨(b : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext ?_⟩
  exact hb'

theorem exists_isPrime_mem_wide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (hq : 5 ≤ q)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (p s : ↥(jIntegralClosure (1 * q) A K))
    (hfsp : (f : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
      (p : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ 𝔫 : Ideal ↥(jIntegralClosure (1 * q) A K), 𝔫.IsPrime ∧ p ∈ 𝔫 ∧
      (∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0 →
          ∀ ht : modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K,
            (⟨_, ht⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔫) := by
  classical
  obtain ⟨-, hloc, -, hmax⟩ :=
    ModularCurve.NodeLocalized.isNoetherianRing_isLocalRing_modularLocalizedAtPoint_coeffSubring red a K x hx ϖ hϖ
  haveI := hloc
  have hmax' := hmax
  have hCle := jIntegralClosure_le_modularLocalizedAtPoint red a ha ha2 h01728 hq K x hx
  let ι := Subring.inclusion hCle
  refine ⟨(IsLocalRing.maximalIdeal _).comap ι, inferInstance, ?_, ?_⟩
  ·
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨w, hw⟩ := hunit.exists_right_inv
    have hpw : (p : LaurentSeries (AlgebraicClosure ℚ)) * (w : LaurentSeries (AlgebraicClosure ℚ)) = 1 :=
      congrArg Subtype.val hw
    have hf0 : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => h₁u (by
      rw [show (⟨_, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 0 from Subtype.ext h, map_zero])
    have hfsw : (f : LaurentSeries (AlgebraicClosure ℚ)) *
        ((s : LaurentSeries (AlgebraicClosure ℚ)) * (w : LaurentSeries (AlgebraicClosure ℚ))) = 1 := by
      rw [← mul_assoc, hfsp, hpw]
    have hfinv : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ =
        (s : LaurentSeries (AlgebraicClosure ℚ)) * (w : LaurentSeries (AlgebraicClosure ℚ)) :=
      inv_eq_of_mul_eq_one_right hfsw
    have hgR : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈
        modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) := by
      rw [hfinv]; exact mul_mem (hCle s.2) w.2
    have hg₁ : (f : LaurentSeries (AlgebraicClosure ℚ))⁻¹ ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red :=
      inv_mem_modularLocalized_of_ne_zero _ _ red h₁ h₁u
    have hmul : (⟨_, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) * ⟨_, hg₁⟩ = 1 :=
      Subtype.ext (mul_inv_cancel₀ hf0)
    have hred_inv : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁⟩ =
        (CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩)⁻¹ := by
      have h := congrArg (CharPReduction.modularRedLocHom (1 * q) A.toSubring red) hmul
      rw [map_mul, map_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hg₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁⟩ ∈ modularFunctionFieldC k 1 := by
      rw [hred_inv]; exact inv_mem h₁F
    have hg0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, hg₁⟩ ≠ 0 := by
      rw [hred_inv]; exact inv_ne_zero h₁u
    have h33 := (ModularCurve.NodeLocalized.natCast_le_ord_modularRedLocHom_iff_mem_sup_span_pow red a ha2 K ϖ hϖ
      ⟨_, hgR⟩ hg₁ hg₁F hg0 0).mpr (by rw [pow_zero, Ideal.span_singleton_one, sup_top_eq]; exact Submodule.mem_top)
    have h33' : ((0 : ℕ) : ℤ) ≤ (frobNodePair q a).1.ord (⟨_, hg₁F⟩ : ↥(modularFunctionFieldC k 1)) := h33
    have hel : (⟨_, hg₁F⟩ : ↥(modularFunctionFieldC k 1)) = (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1))⁻¹ :=
      Subtype.ext (by rw [IntermediateField.coe_inv]; exact hred_inv)
    have hfbar0 : (⟨_, h₁F⟩ : ↥(modularFunctionFieldC k 1)) ≠ 0 := fun h => h₁u (congrArg Subtype.val h)
    have hres : IsLocalRing.residue (frobNodePair q a).1.toValuationSubring ⟨_, hmem⟩ = 0 := by
      by_contra hne
      exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hne)
    have hpos := ord_pos_of_residue_eq_zero_place (frobNodePair q a).1 hmem hfbar0 hres
    rw [hel, Place.ord_inv, Nat.cast_zero] at h33'
    omega
  ·
    intro t ht htC hmemb
    rw [Ideal.mem_comap] at hmemb
    let φ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+*
        ↥(modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q)) :=
      (modularEval (1 * q) (coeffSubring A K)).codRestrict _
        (modularEval_mem_modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q))
    have hιφ : ι ⟨_, htC⟩ = φ t := Subtype.ext rfl
    rw [hιφ] at hmemb
    have hgen0 : φ (MvPolynomial.X 0 - MvPolynomial.C x) ∈ IsLocalRing.maximalIdeal _ := by
      rw [hmax']
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hgen1 : φ (MvPolynomial.X 1 - MvPolynomial.C (x ^ q)) ∈ IsLocalRing.maximalIdeal _ := by
      rw [hmax']
      exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hle : Ideal.span {φ (MvPolynomial.X 0 - MvPolynomial.C x), φ (MvPolynomial.X 1 - MvPolynomial.C (x ^ q))} ≤
        IsLocalRing.maximalIdeal _ := by
      rw [Ideal.span_le]
      rintro g (rfl | rfl)
      · exact hgen0
      · exact hgen1
    have htay := sub_C_eval_mem_span φ x (x ^ q) t
    have hCmem : φ (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] t)) ∈ IsLocalRing.maximalIdeal _ := by
      have h := Ideal.sub_mem _ hmemb (hle htay)
      rwa [sub_sub_cancel] at h
    have hc : redRestrict red K (MvPolynomial.eval ![x, x ^ q] t) =
        pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t := by
      show redRestrict red K (MvPolynomial.eval₂ (RingHom.id _) ![x, x ^ q] t) =
        MvPolynomial.eval₂ (redRestrict red K) ![a, a ^ q] t
      rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
      congr 1
      funext i
      fin_cases i
      · exact hx
      · show redRestrict red K (x ^ q) = a ^ q
        rw [map_pow, hx]
    obtain ⟨d, hd⟩ := exists_mul_eq_one_of_redRestrict_ne_zero red hker K (MvPolynomial.eval ![x, x ^ q] t)
      (by rw [hc]; exact ht)
    have hu : IsUnit (φ (MvPolynomial.C (MvPolynomial.eval ![x, x ^ q] t))) :=
      IsUnit.of_mul_eq_one (φ (MvPolynomial.C d)) (by rw [← map_mul, ← MvPolynomial.C_mul, hd, MvPolynomial.C_1, map_one])
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ hCmem hu)

end

end BdB

namespace BdC

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.NodeLocalized~sub_C_eval_mem_span"

private theorem inv_mem_modularLocalized_of_ne_zero (N : ℕ) [NeZero N] (A : Subring (AlgebraicClosure ℚ))
    {k : Type*} [Field k] (red : A →+* k) {x : LaurentSeries (AlgebraicClosure ℚ)}
    (hx : x ∈ CharPReduction.modularLocalized N A red)
    (hu : CharPReduction.modularRedLocHom N A red ⟨x, hx⟩ ≠ 0) :
    x⁻¹ ∈ CharPReduction.modularLocalized N A red := by
  obtain ⟨r, s, hs, hxs⟩ := id hx
  have hx0 : x ≠ 0 := fun h => hu (by
    rw [show (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) = 0 from Subtype.ext h, map_zero])
  have hloc : CharPReduction.redLoc (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) ≠ 0 := fun h0 =>
    hu (by rw [show CharPReduction.modularRedLocHom N A red ⟨x, hx⟩ = CharPReduction.redLoc ⟨x, hx⟩ from
      CharPReduction.redLocHom_apply _]; exact h0)
  have hspec := CharPReduction.redLoc_spec (⟨x, hx⟩ : CharPReduction.modularLocalized N A red) hxs
  have hr : r ∉ CharPReduction.redKer A red (CharPReduction.modularRing N A)
      (CharPReduction.modularRing_le_integralCoeffs N A) := by
    rw [CharPReduction.notMem_redKer_iff] at hs ⊢
    rw [← hspec]
    exact mul_ne_zero hloc hs
  refine (CharPReduction.mem_localizedAtKer _ _ _ _).mpr ⟨s, r, hr, ?_⟩
  rw [← hxs, inv_mul_cancel_left₀ hx0]

private theorem eq_two_or_eq_three_of_prime_of_lt_five {q : ℕ} (hp : q.Prime) (hq : q < 5) :
    q = 2 ∨ q = 3 := by
  have h2 := hp.two_le
  interval_cases q
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hp (by norm_num)

theorem exists_heightOne_mem_wide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728) (hq : 5 ≤ q)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K)
    (x : ↥(coeffSubring A K)) (hx : redRestrict red K x = a)
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (p s : ↥(jIntegralClosure (1 * q) A K)) (s₀ : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs_eq : (s : LaurentSeries (AlgebraicClosure ℚ)) = modularEval (1 * q) (coeffSubring A K) s₀)
    (hps0 : pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) s₀ ≠ 0)
    (hfsp : (f : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
      (p : LaurentSeries (AlgebraicClosure ℚ))) :
    ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) (_ : 𝔭.IsPrime), 𝔭.height = 1 ∧
      ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 ∧ p ∈ 𝔭 ∧
      (∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K),
        pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0 →
          ∀ ht : modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K,
            (⟨_, ht⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) := by
  classical
  obtain ⟨𝔫, h𝔫, hp𝔫, hS𝔫⟩ :=
    BdB.exists_isPrime_mem_wide red hker a ha ha2 h01728 hq f h₁ h₁F h₁u hmem hnu K
      x hx ϖ hϖ p s hfsp

  have ht : modularEval (1 * q) (coeffSubring A K) s₀ ∈ jIntegralClosure (1 * q) A K := hs_eq ▸ s.2
  have hs𝔫 : s ∉ 𝔫 := by
    rw [show s = ⟨modularEval (1 * q) (coeffSubring A K) s₀, ht⟩ from Subtype.ext hs_eq]
    exact hS𝔫 s₀ hps0 ht

  have hf0 : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => h₁u (by
    rw [show (⟨_, h₁⟩ : CharPReduction.modularLocalized (1 * q) A.toSubring red) = 0 from Subtype.ext h, map_zero])
  have hs0 : (s : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h =>
    hs𝔫 (by rw [show s = 0 from Subtype.ext h]; exact 𝔫.zero_mem)
  have hp0 : p ≠ 0 := fun h => by
    have h' := hfsp
    rw [h, ZeroMemClass.coe_zero] at h'
    exact mul_ne_zero hf0 hs0 h'

  haveI := h𝔫
  obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr hp𝔫)
  have h𝔭pr : 𝔭.IsPrime := h𝔭min.1.1
  have hp𝔭 : p ∈ 𝔭 := h𝔭min.1.2 (Ideal.mem_span_singleton_self p)

  haveI hN : IsNoetherianRing ↥(jIntegralClosure (1 * q) A K) := by
    obtain ⟨data, -⟩ := ModularCurve.exists_modularPolynomialData_evalSymm q
    exact (ModularCurve.jIntegralClosure_isNoetherian_and_isLocalization red a data K).1
  haveI : (Ideal.span {p}).IsPrincipal := ⟨⟨p, rfl⟩⟩
  have hle1 : 𝔭.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) 𝔭 h𝔭min
  have hge1 : 1 ≤ 𝔭.height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp0)).trans
      (Ideal.height_mono h𝔭min.1.2)
  have hht : 𝔭.height = 1 := le_antisymm hle1 hge1

  have hq𝔭 : ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 := by
    intro hq𝔭
    haveI := h𝔭pr
    have hg : ((f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        fieldOver (1 * q) K := by
      rw [IntermediateField.coe_inv]; exact inv_mem hfK
    have hg₁ : ((f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) ∈
        CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [IntermediateField.coe_inv]; exact inv_mem_modularLocalized_of_ne_zero _ _ _ h₁ h₁u
    have hg₂ : ((frickeInvolutionBar (1 * q) f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) :
          LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red := by
      rw [map_inv₀, IntermediateField.coe_inv]; exact inv_mem_modularLocalized_of_ne_zero _ _ _ h₂ h₂u
    obtain ⟨r₁, s₁, hs₁, hr₁⟩ :=
      ModularCurve.exists_mul_eq_of_height_one_of_natCast_mem red K 𝔭 hht hq𝔭 f⁻¹ hg hg₁ hg₂
    rw [IntermediateField.coe_inv] at hr₁
    have hs₁f : (s₁ : LaurentSeries (AlgebraicClosure ℚ)) =
        (f : LaurentSeries (AlgebraicClosure ℚ)) * (r₁ : LaurentSeries (AlgebraicClosure ℚ)) := by
      rw [← hr₁, mul_inv_cancel_left₀ hf0]
    have hC : s₁ * s = p * r₁ := Subtype.ext (by
      show (s₁ : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
        (p : LaurentSeries (AlgebraicClosure ℚ)) * (r₁ : LaurentSeries (AlgebraicClosure ℚ))
      rw [hs₁f, ← hfsp]; ring)
    have hmul : s₁ * s ∈ 𝔭 := hC ▸ Ideal.mul_mem_right _ _ hp𝔭
    rcases h𝔭pr.mem_or_mem hmul with h | h
    · exact hs₁ h
    · exact hs𝔫 (h𝔭le h)
  exact ⟨𝔭, h𝔭pr, hht, hq𝔭, hp𝔭, fun t ht0 ht' hmem => hS𝔫 t ht0 ht' (h𝔭le hmem)⟩

end BdC

namespace BdD

open AlgebraicCurve IsLocalRing ModularCurve
p2m_open "ModularCurve.NodeLocalized~sub_C_eval_mem_span"

noncomputable section

open Polynomial in

private scoped instance instIsAlgClosedResidueField_reMint {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ (fun f hf_monic hf_irr => ?_)
  have hf_lifts : f ∈ lifts (IsLocalRing.residue A) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => IsLocalRing.residue_surjective (f.coeff n)
  obtain ⟨g, hg_map, -, hg_monic⟩ := lifts_and_degree_eq_and_monic hf_lifts hf_monic
  have hgL_deg : (g.map (algebraMap A L)).degree ≠ 0 := by
    rw [hg_monic.degree_map]
    intro h0
    have hg_nat : g.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h0)
    have hf_deg : f.natDegree = 0 := by
      rw [← hg_map, hg_monic.natDegree_map]; exact hg_nat
    exact hf_irr.not_isUnit (by rw [(hf_monic.natDegree_eq_zero).mp hf_deg]; exact isUnit_one)
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hgL_deg
  have hα_int : IsIntegral A α := ⟨g, hg_monic, by rwa [IsRoot.def, eval_map] at hα⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hα_int
  refine ⟨IsLocalRing.residue A a, ?_⟩
  have hga : g.eval a = 0 := by
    have : algebraMap A L (g.eval a) = 0 := by
      rw [show algebraMap A L (g.eval a) = (g.map (algebraMap A L)).eval α from by
        rw [← ha, eval_map, eval₂_hom]]
      exact hα
    exact (map_eq_zero_iff _ Subtype.coe_injective).mp this
  rw [show f.eval (IsLocalRing.residue A a) = IsLocalRing.residue A (g.eval a) from by
    rw [← hg_map, eval_map, eval₂_hom], hga, map_zero]

private theorem withZero_eq_one_of_log_eq_zero
    (x : WithZero (Multiplicative ℤ)) (hne : x ≠ 0) (hlog : WithZero.log x = 0) : x = 1 := by
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.mp hne
  rw [show (1 : WithZero (Multiplicative ℤ)) = ((1 : Multiplicative ℤ) : WithZero _) from rfl,
    WithZero.coe_inj]
  have hta : Multiplicative.toAdd m = (0 : ℤ) := hlog
  exact Multiplicative.toAdd.injective (by rw [hta]; rfl)

private theorem inv_mem_of_isUnit {F : Type*} [Field F] (V : ValuationSubring F)
    (f : F) (hfW : f ∈ V) (hu : IsUnit (⟨f, hfW⟩ : V)) : f⁻¹ ∈ V := by
  obtain ⟨u, hueq⟩ := hu
  have h1 : ((↑u⁻¹ : ↥V) : F) = f⁻¹ := by
    have h2 : ((↑u : ↥V) : F) = f := by rw [hueq]
    have h3 : ((↑u : ↥V) : F) * ((↑u⁻¹ : ↥V) : F) = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
    rw [h2] at h3
    exact eq_inv_of_mul_eq_one_right h3
  exact h1 ▸ (↑u⁻¹ : ↥V).2

private theorem eq_two_or_eq_three_of_prime_of_lt_five {q : ℕ} (hp : q.Prime) (hq : q < 5) :
    q = 2 ∨ q = 3 := by
  have h2 := hp.two_le
  interval_cases q
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd hp (by norm_num)

private theorem mem_range_red_of_pow_q_sq_eq_self {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] [CharP k q] [IsAlgClosed k]
    (red : A →+* k) (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha2 : a ^ (q ^ 2) = a) : a ∈ Set.range red := by
  classical
  have hH : ∀ c ∈ IsLocalRing.maximalIdeal (↥A), red c = 0 := fun c hc => (hker c).mpr hc
  haveI h2s : (IsLocalRing.maximalIdeal (↥A)).IsTwoSided := inferInstance
  let φ : IsLocalRing.ResidueField ↥A →+* k :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red hH
  have hred : ∀ c : ↥A, red c = φ (IsLocalRing.residue A c) := fun c =>
    (Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥A) red hH).symm
  letI : Algebra (IsLocalRing.ResidueField ↥A) k := φ.toAlgebra
  haveI hRFac : IsAlgClosed (IsLocalRing.ResidueField ↥A) := instIsAlgClosedResidueField_reMint A
  have halg : IsIntegral (IsLocalRing.ResidueField ↥A) a := by
    refine ⟨Polynomial.X ^ (q^2) - Polynomial.X, ?_, ?_⟩
    · refine (Polynomial.monic_X_pow (q^2)).sub_of_left ?_
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      exact_mod_cast Nat.one_lt_pow two_ne_zero (Fact.out : q.Prime).two_le
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
      exact sub_eq_zero_of_eq ha2
  have hdeg : (minpoly (IsLocalRing.ResidueField ↥A) a).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible halg)
  obtain ⟨b, hb⟩ := minpoly.mem_range_of_degree_eq_one (IsLocalRing.ResidueField ↥A) a hdeg
  obtain ⟨c, hc⟩ := IsLocalRing.residue_surjective (R := ↥A) b
  exact ⟨c, by rw [hred c, hc]; exact hb⟩

private theorem exists_mul_eq_one_of_redRestrict_ne_zero
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) :
    ∃ d : ↥(coeffSubring A K), c * d = 1 := by
  let cA : A := Subring.inclusion (inf_le_left : coeffSubring A K ≤ A.toSubring) c
  have hcA : cA ∉ IsLocalRing.maximalIdeal A := fun h => hc ((hker cA).mpr h)
  obtain ⟨b, hb⟩ := (IsLocalRing.notMem_maximalIdeal.mp hcA).exists_right_inv
  have hb' : (c : AlgebraicClosure ℚ) * (b : AlgebraicClosure ℚ) = 1 := congrArg Subtype.val hb
  have hc0 : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hb'; exact zero_ne_one hb'
  have hbinv : (b : AlgebraicClosure ℚ) = (c : AlgebraicClosure ℚ)⁻¹ := eq_inv_of_mul_eq_one_right hb'
  have hbK : (b : AlgebraicClosure ℚ) ∈ K.toSubalgebra.toSubring := by
    rw [hbinv]
    exact K.inv_mem (Subring.mem_inf.mp c.2).2
  refine ⟨⟨(b : AlgebraicClosure ℚ), Subring.mem_inf.mpr ⟨b.2, hbK⟩⟩, Subtype.ext ?_⟩
  exact hb'

private theorem exists_uniformizer_coeffSubring
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] :
    ∃ ϖ : ↥(coeffSubring A K), ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d := by
  rcases ModularCurve.NodeLocalized.coeffSubring_eq_or_isDiscreteValuationRing A K with hEq | hDVR
  · exfalso
    have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
    have hinv : (q : AlgebraicClosure ℚ)⁻¹ ∈ coeffSubring A K := by
      rw [hEq]
      show (q : AlgebraicClosure ℚ)⁻¹ ∈ K
      exact inv_mem (natCast_mem K q)
    have hcoe : (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) :=
      map_natCast (coeffSubring A K).subtype q
    have hone : ((q : ℕ) : ↥(coeffSubring A K)) * ⟨_, hinv⟩ = 1 := by
      apply Subtype.ext
      show (((q : ℕ) : ↥(coeffSubring A K)) : AlgebraicClosure ℚ) * (q : AlgebraicClosure ℚ)⁻¹ = 1
      rw [hcoe, mul_inv_cancel₀ hq0]
    have h := congrArg (redRestrict red K) hone
    rw [map_mul, map_natCast, CharP.cast_eq_zero k q, zero_mul, map_one] at h
    exact zero_ne_one h
  · haveI := hDVR
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥(coeffSubring A K)
    have hmax : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    refine ⟨ϖ, fun c => ⟨fun hc0 => ?_, ?_⟩⟩
    · have hcm : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        obtain ⟨d, hd⟩ := hu.exists_right_inv
        have h := congrArg (redRestrict red K) hd
        rw [map_mul, hc0, zero_mul, map_one] at h
        exact zero_ne_one h
      rw [hmax, Ideal.mem_span_singleton'] at hcm
      obtain ⟨d, hd⟩ := hcm
      exact ⟨d, by rw [← hd, mul_comm]⟩
    · rintro ⟨d, rfl⟩
      rw [map_mul]
      suffices hϖ0 : redRestrict red K ϖ = 0 by rw [hϖ0, zero_mul]
      by_contra hne
      obtain ⟨e, he⟩ := exists_mul_eq_one_of_redRestrict_ne_zero red hker K ϖ hne
      exact hϖ.not_isUnit (IsUnit.of_mul_eq_one e he)

theorem core_wide
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) (h01728 : a = 0 ∨ a = 1728)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hmem : (⟨_, h₁F⟩ : modularFunctionFieldC k 1) ∈ (frobNodePair q a).1.toValuationSubring)
    (hnu : ¬IsUnit (⟨_, hmem⟩ : (frobNodePair q a).1.toValuationSubring))
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (hq : 5 ≤ q) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hx : ∃ x : ↥(coeffSubring A K), redRestrict red K x = a)
    (hfK : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K) :
    False := by
  have hfR : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈
      modularLocalizedAtPoint (1 * q) (coeffSubring A K) (redRestrict red K) a (a ^ q) :=
    ModularCurve.NodeLocalized.mem_modularLocalizedAtPoint_coeffSubring_of_isIntegral_of_mem_fieldOver
      red hker hq a ha ha2 f h₁ h₁F h₁u h₂ h₂F h₂u hford K hx hfK
  have hMC :=
    BdA.exists_mul_eq_mem_jIntegralClosure_wide red hker a ha ha2
      f h₁ h₁F h₁u h₂ h₂F h₂u hmem hnu K hfK hfR
  obtain ⟨p, s, s₀, hs_eq, hps0, hfsp⟩ := hMC

  obtain ⟨x, hxa⟩ := hx
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer_coeffSubring red hker K
  have hpBlock :
      ∃ (𝔭 : Ideal ↥(jIntegralClosure (1 * q) A K)) (_ : 𝔭.IsPrime), 𝔭.height = 1 ∧
        ((q : ℕ) : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭 ∧ p ∈ 𝔭 ∧
        (∀ t : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          pointEval (coeffSubring A K) (redRestrict red K) a (a ^ q) t ≠ 0 →
            ∀ ht : modularEval (1 * q) (coeffSubring A K) t ∈ jIntegralClosure (1 * q) A K,
              (⟨_, ht⟩ : ↥(jIntegralClosure (1 * q) A K)) ∉ 𝔭) :=
    BdC.exists_heightOne_mem_wide red hker a ha ha2 h01728 hq f h₁ h₁F h₁u h₂ h₂u
      hmem hnu K hfK x hxa ϖ hϖ p s s₀ hs_eq hps0 hfsp
  obtain ⟨𝔭, hpr, h𝔭1, hq𝔭, hp𝔭, h𝔭S⟩ := hpBlock
  haveI := hpr
  have hs_eq' : s = ⟨modularEval (1 * q) (coeffSubring A K) s₀, hs_eq ▸ s.2⟩ := Subtype.ext hs_eq
  have hs𝔭 : s ∉ 𝔭 := hs_eq' ▸ h𝔭S s₀ hps0 (hs_eq ▸ s.2)
  have h653 :=
    ModularCurve.exists_place_centred_node_of_height_one_of_natCast_notMem red a K 𝔭 h𝔭1 hq𝔭 h𝔭S
  obtain ⟨W, hWc, hWiff⟩ := h653
  have hord : W.ord f = 0 := hford W hWc

  have hf0 : (f : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro hf0; apply h₁u
    have hz : (⟨_, h₁⟩ : ↥(CharPReduction.modularLocalized (1 * q) A.toSubring red)) = 0 := by
      apply Subtype.ext
      show (f : LaurentSeries (AlgebraicClosure ℚ)) = 0
      calc (f : LaurentSeries (AlgebraicClosure ℚ))
          = ((0 : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) := by rw [hf0]
        _ = 0 := Subfield.coe_zero _
    rw [hz]; exact map_zero _
  have hfW : f ∈ W.toValuationSubring := (hWiff f hfK).mp ⟨p, s, hs𝔭, hfsp⟩
  have hfinvK : (f⁻¹ : LaurentSeries (AlgebraicClosure ℚ)) ∈ fieldOver (1 * q) K :=
    (fieldOver (1 * q) K).inv_mem hfK
  have hval1 : W.adicValuation f = 1 :=
    withZero_eq_one_of_log_eq_zero _ (W.adicValuation_ne_zero hf0)
      (by have := hord; unfold Place.ord at this; omega)
  have hfinvW : f⁻¹ ∈ W.toValuationSubring :=
    inv_mem_of_isUnit W.toValuationSubring f hfW
      ((W.adicValuation_coe_eq_one_iff _).mp hval1)
  have hWfi := (hWiff f⁻¹ hfinvK).mpr hfinvW
  obtain ⟨r', s', hs'𝔭, hfs'⟩ := hWfi
  have hf0L : (f : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := fun h => hf0 (by
    apply Subtype.ext; rw [h]; exact (Subfield.coe_zero _).symm)
  have hs'fr : (s' : LaurentSeries (AlgebraicClosure ℚ)) =
      (f : LaurentSeries (AlgebraicClosure ℚ)) * (r' : LaurentSeries (AlgebraicClosure ℚ)) := by
    have hcoe : ((f⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ((f : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))⁻¹ := by
      exact_mod_cast rfl
    rw [hcoe, inv_mul_eq_iff_eq_mul₀ hf0L] at hfs'
    exact hfs'
  have key : s' * s = p * r' := by
    apply Subtype.ext
    show (s' : LaurentSeries (AlgebraicClosure ℚ)) * (s : LaurentSeries (AlgebraicClosure ℚ)) =
      (p : LaurentSeries (AlgebraicClosure ℚ)) * (r' : LaurentSeries (AlgebraicClosure ℚ))
    rw [hs'fr, ← hfsp]; ring
  have hin : p * r' ∈ 𝔭 := 𝔭.mul_mem_right r' hp𝔭
  have hout : s' * s ∉ 𝔭 := fun h => (hpr.mem_or_mem h).elim hs'𝔭 hs𝔭
  exact hout (key ▸ hin)

end

end BdD
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero_of_mem_ssJSet.BdD"

namespace BdWrap
open AlgebraicCurve IsLocalRing ModularCurve

theorem not_isUnit_of_hasValue_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    {P : Place K F} {g : F} (hc : P.HasValue g 0) :
    ¬IsUnit (⟨g, hc.mem⟩ : P.toValuationSubring) := by
  intro hu
  have hres := (residue_ne_zero_iff_isUnit (⟨g, hc.mem⟩ : P.toValuationSubring)).mpr hu
  apply hres
  have := hc.residue_eq
  rwa [map_zero] at this
end BdWrap
p2m_reactivate "P2MW.S_ModularCurve_NodeLocalized_ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero_of_mem_ssJSet.BdD"

p2m_open "ModularCurve.NodeLocalized~sub_C_eval_mem_span" in open AlgebraicCurve IsLocalRing ModularCurve  in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k] (red : A →+* k)
    (hker : ∀ c : A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A) (hq : 5 ≤ q)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (h₂ : ((frickeInvolutionBar (1 * q) f : modularFunctionFieldBar (1 * q)) : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₂F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ∈ modularFunctionFieldC k 1)
    (h₂u : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₂⟩ ≠ 0)
    (hford : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)))) → W.ord f = 0)
    (c : k) (hc₁ : (frobNodePair q a).1.HasValue (⟨_, h₁F⟩ : modularFunctionFieldC k 1) c) :
    c ≠ 0 := by
  intro hc
  subst hc
  have hnu := BdWrap.not_isUnit_of_hasValue_zero hc₁
  by_cases h01728 : a = 0 ∨ a = 1728
  ·
    have hred_a : a ∈ Set.range red := BdD.mem_range_red_of_pow_q_sq_eq_self red hker a ha2
    obtain ⟨K, hKfd, hfK, hx⟩ :=
      ModularCurve.exists_finiteDimensional_mem_fieldOver_and_redRestrict_eq A red a hred_a f
    haveI := hKfd
    exact (BdD.core_wide red hker a ha ha2 h01728 f h₁ h₁F h₁u h₂ h₂F h₂u hc₁.mem hnu hford hq K hx hfK).elim
  · obtain ⟨h0, h1728⟩ := not_or.mp h01728
    obtain ⟨W₀, hW₀c, hW₀ord⟩ :=
      ModularCurve.NodeLocalized.exists_centred_ord_ne_zero_of_not_isUnit_frobNodePair
        red hker a ha ha2 h0 h1728 f h₁ h₁F h₁u h₂ h₂F h₂u hc₁.mem hnu
    exact hW₀ord (hford W₀ hW₀c)

end S_ModularCurve_NodeLocalized_ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero_of_mem_ssJSet
end P2MW
export P2MW.S_ModularCurve_NodeLocalized_ne_zero_of_hasValue_frobNodePair_of_forall_centred_ord_eq_zero_of_mem_ssJSet (solution)
