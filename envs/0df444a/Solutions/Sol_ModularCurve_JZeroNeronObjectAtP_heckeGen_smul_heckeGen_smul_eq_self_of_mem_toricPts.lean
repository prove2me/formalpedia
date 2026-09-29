-- Prove2me | solution 1 for ModularCurve.JZeroNeronObjectAtP.heckeGen_smul_heckeGen_smul_eq_self_of_mem_toricPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/185d6e91-ab1f-5ea7-a95a-06c722b7ebf7

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeOperatorBar_self_add_atkinLehner_smul
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_toricPts_le_ker_degeneracyPushforwardPair
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_smul_mem_toricPts
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronObjectAtP_heckeGen_smul_heckeGen_smul_eq_self_of_mem_toricPts
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply"
p2m_attr_erase "simp" "CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_JZeroNeronObjectAtP_heckeGen_smul_heckeGen_smul_eq_self_of_mem_toricPts.ModularCurve ModularCurve.JZeroNeronObjectAtP"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronObjectAtP.LevelData JZeroNeronObjectAtP heckeOperatorBar HeckeOperatorsCommuteBar heckeEvalBar heckeEvalBar_heckeGen heckeModuleBar JZero modularFunctionFieldFull HeckeAlg heckeGen geomAut heckeOperatorBar_self_add_atkinLehner_smul atkinLehnerInvolutionFull JZeroNeronObjectAtP.toricPts_le_ker_degeneracyPushforwardPair JZeroNeronObjectAtP.smul_mem_toricPts atkinLehnerInvolutionFull_apply_apply heckeOperatorsCommuteBar"
namespace InvJ0
p2m_open "ModularCurve"

theorem heckeGen_smul_eq (N : ℕ) [NeZero N] (h : HeckeOperatorsCommuteBar N) (ℓ : Nat.Primes) (y : JZero N) :
    (letI := heckeModuleBar N; (heckeGen ℓ : HeckeAlg) • y) = heckeOperatorBar N ℓ y := by
  have hinst : heckeModuleBar N = Module.compHom (JZero N) (heckeEvalBar h) := dif_pos h
  show @HSMul.hSMul HeckeAlg (JZero N) (JZero N) (@instHSMul HeckeAlg (JZero N) (heckeModuleBar N).toSMul) (heckeGen ℓ) y = _
  rw [hinst]
  show (heckeEvalBar h (heckeGen ℓ)) y = _
  rw [heckeEvalBar_heckeGen]

theorem geomAut_atkinLehnerInvolutionFull_mul_self (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) :
    geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p) *
      geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p) = 1 := by
  rw [← map_mul]
  have h1 : atkinLehnerInvolutionFull N₀ p * atkinLehnerInvolutionFull N₀ p = 1 :=
    AlgEquiv.ext fun f => by
      rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
      exact atkinLehnerInvolutionFull_apply_apply N₀ p hpN₀ f
  rw [h1, map_one]

end ModularCurve.InvJ0

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    letI := heckeModuleBar (N₀ * p)
    ∀ (m : ℕ), 0 < m → ∀ x ∈ O.toricPts m,
      (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • ((heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • x) = x := by
  letI := heckeModuleBar (N₀ * p)
  intro m hm x hx
  have hc : HeckeOperatorsCommuteBar (N₀ * p) := ModularCurve.heckeOperatorsCommuteBar (N₀ * p)
  have hU : ∀ y : JZero (N₀ * p), (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • y = heckeOperatorBar (N₀ * p) ⟨p, Fact.out⟩ y :=
    fun y => ModularCurve.InvJ0.heckeGen_smul_eq (N₀ * p) hc ⟨p, Fact.out⟩ y

  have h714 := ModularCurve.heckeOperatorBar_self_add_atkinLehner_smul N₀ p (Fact.out) hpN₀
  have hUeq : ∀ y ∈ O.toricPts m, heckeOperatorBar (N₀ * p) ⟨p, Fact.out⟩ y =
      -(geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p) • y) := by
    intro y hy
    obtain ⟨hα, -⟩ := ModularCurve.JZeroNeronObjectAtP.toricPts_le_ker_degeneracyPushforwardPair N₀ p hpN₀ A hA Λ hΛ O m hm y hy
    have h := h714 y
    rw [hα, map_zero] at h
    exact eq_neg_of_add_eq_zero_left h

  have hUx_mem : (heckeGen ⟨p, Fact.out⟩ : HeckeAlg) • x ∈ O.toricPts m :=
    ModularCurve.JZeroNeronObjectAtP.smul_mem_toricPts N₀ p hpN₀ A hA Λ hΛ O m hm _ x hx
  rw [hU] at hUx_mem

  have hww : geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p) •
      (geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (N₀ * p)) (atkinLehnerInvolutionFull N₀ p) • x) = x := by
    rw [← mul_smul, ModularCurve.InvJ0.geomAut_atkinLehnerInvolutionFull_mul_self N₀ p hpN₀, one_smul]
  rw [hU, hU, hUeq _ hUx_mem, hUeq x hx, smul_neg, neg_neg, hww]

end S_ModularCurve_JZeroNeronObjectAtP_heckeGen_smul_heckeGen_smul_eq_self_of_mem_toricPts
end P2MW
export P2MW.S_ModularCurve_JZeroNeronObjectAtP_heckeGen_smul_heckeGen_smul_eq_self_of_mem_toricPts (solution)
