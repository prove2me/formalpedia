-- Prove2me | solution 1 for ModularCurve.JZero.jensen_arch_at_of_nonCuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e28f4c08-eaac-5d79-8b31-58a0be591d7c

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_ModularCurve_JZero_jensen_arch_embedding
import Theorems.Thm_ModularCurve_JZero_exists_seq_tendsto_place
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_arch_at_of_nonCuspidal
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.qExpandAlgHomC_apply ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false

open AlgebraicCurve ModularCurve Filter Topology

noncomputable section

namespace P2MJA

theorem exists_embedding_of_infinitePlace (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
    (ν : NumberField.InfinitePlace ↥L) :
    ∃ σ : (AlgebraicClosure ℚ) →+* ℂ, ∀ a : ↥L, ν a = ‖σ (a : AlgebraicClosure ℚ)‖ := by
  letI algLC : Algebra ↥L ℂ := RingHom.toAlgebra ν.embedding
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic ↥L (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥L
  let σ₀ : (AlgebraicClosure ℚ) →ₐ[↥L] ℂ := IsAlgClosed.lift
  refine ⟨σ₀.toRingHom, fun a => ?_⟩
  have hcomm : σ₀.toRingHom ((a : ↥L) : AlgebraicClosure ℚ) = ν.embedding a := by
    have h1 := σ₀.commutes a
    have h3 : (algebraMap ↥L ℂ) a = ν.embedding a := by rw [RingHom.algebraMap_toAlgebra]
    rw [h3] at h1
    exact h1
  rw [hcomm]
  exact (NumberField.InfinitePlace.norm_embedding_eq ν a).symm

theorem prox_transport {L : IntermediateField ℚ (AlgebraicClosure ℚ)} (σ : (AlgebraicClosure ℚ) →+* ℂ)
    {r : ℕ} (x y : Fin r → ↥L) (ex ey : Fin r → AlgebraicClosure ℚ)
    (hx : ∀ i, ((x i : ↥L) : AlgebraicClosure ℚ) = ex i) (hy : ∀ i, ((y i : ↥L) : AlgebraicClosure ℚ) = ey i)
    (ν : ↥L → ℝ) (hν : ∀ a : ↥L, ν a = ‖σ (a : AlgebraicClosure ℚ)‖) :
    prox ν x y = prox (fun a => ‖σ a‖) ex ey := by
  unfold prox
  have hA : (⨆ i, ν (x i)) = ⨆ i, ‖σ (ex i)‖ := iSup_congr fun i => by rw [hν, hx]
  have hB : (⨆ i, ν (y i)) = ⨆ i, ‖σ (ey i)‖ := iSup_congr fun i => by rw [hν, hy]
  have hC : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1))
      = ⨆ p : Fin r × Fin r, ‖σ (ex p.1 * ey p.2 - ex p.2 * ey p.1)‖ := by
    refine iSup_congr fun p => ?_
    rw [hν]
    congr 1
    have : ((x p.1 * y p.2 - x p.2 * y p.1 : ↥L) : AlgebraicClosure ℚ) = ex p.1 * ey p.2 - ex p.2 * ey p.1 := by
      push_cast; rw [hx, hx, hy, hy]
    rw [this]
  rw [hA, hB, hC]

variable (N : ℕ) [NeZero N]

def pointFun {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (k : ℕ) (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  (B.sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v) (evalVec s w))
    - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s v i)‖) - Real.log ‖σ (secVal s v k u)‖)

def genFun {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (k : ℕ) (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) : ℝ :=
  ((B.erase v₀).sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w))
    - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
        + (B v₀ : ℝ) * Real.log (⨆ q : Fin r × Fin r,
            ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖)
        - Real.log ‖σ (regVal s v₀ t k (B v₀).toNat u)‖)

theorem genFun_of_apply_eq_zero {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (σ : (AlgebraicClosure ℚ) →+* ℂ)
    (k : ℕ) (u : modularFunctionFieldBar N) (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (h0 : B v₀ = 0) :
    genFun N s σ k u B v₀ t = pointFun N s σ k u B v₀ := by
  classical
  unfold genFun pointFun
  have herase : B.erase v₀ = B := by
    rw [Finsupp.erase_of_notMem_support]; rwa [Finsupp.notMem_support_iff]
  have hreg : regVal s v₀ t k (B v₀).toNat u = secVal s v₀ k u := by
    rw [h0, Int.toNat_zero, regVal, secVal]
    simp only [dif_pos hr, pow_zero, mul_one]
  rw [herase, hreg, h0]
  push_cast
  ring

theorem abs_add_le_of_tendsto {f : ℕ → ℝ} {G m M : ℝ} (hf : Tendsto f atTop (𝓝 G)) (h : ∀ n, |f n + m| ≤ M) :
    |G + m| ≤ M := by
  have h1 : Tendsto (fun n => |f n + m|) atTop (𝓝 |G + m|) := (hf.add_const m).abs
  exact le_of_tendsto' h1 h

def ATShape {r : ℕ} (s : Fin r → modularFunctionFieldBar N)
    (Adm : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Prop) : Prop :=
  ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
    u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
    ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
    ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
      Adm v₀ → 0 < B v₀ → v₀.ord t = 1 →
      ∃ vseq : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ n, B (vseq n) = 0) ∧ Tendsto (fun n => pointFun N s σ k u B (vseq n)) atTop (𝓝 (genFun N s σ k u B v₀ t))

set_option maxHeartbeats 3200000 in

theorem jensen_arch_at_of_AT {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (Adm : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Prop) (hAT : ATShape N s Adm) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.InfinitePlace ↥L),
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : modularFunctionFieldBar N), (0 < B v₀ → Adm v₀) → (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        |((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
              + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m)|
          ≤ c₀ * k := by
  classical

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (cuspInftyBar N).toValuationSubring
  have htinf : (cuspInftyBar N).ord (π : modularFunctionFieldBar N) = 1 := (cuspInftyBar N).ord_coe_irreducible hπ
  obtain ⟨c, hc⟩ := ModularCurve.JZero.jensen_arch_embedding N s hs (π : modularFunctionFieldBar N) htinf
  obtain ⟨i₀, -⟩ := ModularCurve.exists_ord_add_embDivisor_eq_zero N s hs (cuspInftyBar N)
  have hr : 0 < r := i₀.pos
  refine ⟨c, ?_⟩
  intro k u hu0 hu B hB L _ ν x hx
  obtain ⟨σ, hσ⟩ := exists_embedding_of_infinitePlace L ν
  obtain ⟨m, -, hpoint⟩ := hc σ k u hu0 hu B hB
  refine ⟨m, fun v₀ t hadm ht hx₀ cc hcc y hy hy0 => ?_⟩
  have hBnn : 0 ≤ B v₀ := by
    rw [hB v₀]
    have := ((mem_riemannRochSpace_iff.mp hu) v₀).resolve_left hu0
    linarith

  have hσline : |genFun N s σ k u B v₀ t + m| ≤ c * k := by
    by_cases h0 : B v₀ = 0
    · rw [genFun_of_apply_eq_zero N hr s σ k u B v₀ t h0]
      have := hpoint v₀ h0
      unfold pointFun
      rw [show ∀ a b d : ℝ, a - (b - d - m) = a - (b - d) + m from fun a b d => by ring] at this
      exact this
    · have hpos : 0 < B v₀ := lt_of_le_of_ne hBnn (Ne.symm h0)
      obtain ⟨vseq, hvseq0, hlim⟩ := hAT σ k u hu0 hu B hB v₀ t (hadm hpos) hpos (ht hpos)
      refine abs_add_le_of_tendsto hlim fun n => ?_
      have := hpoint (vseq n) (hvseq0 n)
      unfold pointFun
      rw [show ∀ a b d : ℝ, a - (b - d - m) = a - (b - d) + m from fun a b d => by ring] at this
      exact this

  have hsum : ((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
      = (B.erase v₀).sum fun w n => (n : ℝ) * prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w) := by
    refine Finsupp.sum_congr fun w hw => ?_
    have hw' : w ∈ B.support := by
      rw [Finsupp.support_erase] at hw
      exact Finset.mem_of_mem_erase hw
    congr 1
    exact prox_transport σ (x v₀) (x w) (evalVec s v₀) (evalVec s w) hx₀ (hx w hw') (ν : ↥L → ℝ) hσ
  have hsup : (⨆ i, (ν (x v₀ i) : ℝ)) = ⨆ i, ‖σ (evalVec s v₀ i)‖ := iSup_congr fun i => by rw [hσ, hx₀]
  have hcval : (ν cc : ℝ) = ‖σ (regVal s v₀ t k (B v₀).toNat u)‖ := by rw [hσ, hcc]
  rw [hsum, hsup, hcval]
  by_cases hpos : 0 < B v₀
  · have hysup : (⨆ q, (ν (y q) : ℝ)) = ⨆ q : Fin r × Fin r,
        ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖ :=
      iSup_congr fun q => by rw [hσ, hy hpos q]
    rw [hysup]
    unfold genFun at hσline
    rw [show ∀ a b : ℝ, a - (b - m) = a - b + m from fun a b => by ring]
    exact hσline
  · have h0 : B v₀ = 0 := le_antisymm (not_lt.mp hpos) hBnn
    unfold genFun at hσline
    rw [h0] at hσline ⊢
    push_cast at hσline ⊢
    simp only [mul_zero, zero_mul, add_zero, sub_zero] at hσline ⊢
    rw [show ∀ a b : ℝ, a - (b - m) = a - b + m from fun a b => by ring]
    simpa using hσline

end P2MJA

end

namespace P2MJA

open Filter Topology

variable (N : ℕ) [NeZero N]

def ATWs23 {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (jhat : modularFunctionFieldBar N) : Prop :=
  ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N),
    v₀.ord t = 1 → (v₀ = cuspInftyBar N ∨ jhat ∈ v₀.toValuationSubring) →
    ∀ (σ : (AlgebraicClosure ℚ) →+* ℂ) (S : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
      (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 → u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
    ∀ e : ℕ, (e : ℤ) = v₀.ord u + k * embDivisor N v₀ →
    ∃ v : ℕ → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ v₀) ∧
      (∀ w ∈ S, w ≠ v₀ → Tendsto (fun n => prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s w)) atTop
          (𝓝 (prox (fun a => ‖σ a‖) (evalVec s v₀) (evalVec s w)))) ∧
      Tendsto (fun n => (k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖
          - (e : ℝ) * prox (fun a => ‖σ a‖) (evalVec s (v n)) (evalVec s v₀)) atTop
        (𝓝 (((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
            + (e : ℝ) * Real.log (⨆ q : Fin r × Fin r,
                ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖)
            - Real.log ‖σ (regVal s v₀ t k e u)‖))

theorem ATShape_of_ws23 {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (jhat : modularFunctionFieldBar N)
    (hAT : ATWs23 N s jhat) :
    ATShape N s (fun v₀ => v₀ = cuspInftyBar N ∨ jhat ∈ v₀.toValuationSubring) := by
  classical
  intro σ k u hu0 hu B hB v₀ t hadm hpos ht
  set e : ℕ := (B v₀).toNat with he_def
  have hBnn : 0 ≤ B v₀ := hpos.le
  have heZ : (e : ℤ) = B v₀ := Int.toNat_of_nonneg hBnn
  have heR : (e : ℝ) = (B v₀ : ℝ) := by exact_mod_cast heZ
  have he : (e : ℤ) = v₀.ord u + k * embDivisor N v₀ := by
    rw [heZ, hB v₀, Finsupp.smul_apply, smul_eq_mul]
  obtain ⟨v, hvS, hvne, hprox, hcore⟩ := hAT v₀ t ht hadm σ B.support k u hu0 hu e he
  refine ⟨v, fun n => Finsupp.notMem_support_iff.mp (hvS n), ?_⟩
  have hv₀mem : v₀ ∈ B.support := Finsupp.mem_support_iff.mpr (ne_of_gt hpos)

  set Pr : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → ℝ :=
    fun a b => prox (fun z => ‖σ z‖) (evalVec s a) (evalVec s b) with hPr
  have hsplit : ∀ n, pointFun N s σ k u B (v n)
      = (∑ w ∈ B.support.erase v₀, (B w : ℝ) * Pr (v n) w)
        - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖
            - (e : ℝ) * Pr (v n) v₀) := by
    intro n
    unfold pointFun
    rw [Finsupp.sum, ← Finset.add_sum_erase _ _ hv₀mem, heR]
    simp only [hPr]
    ring
  have hlimit : genFun N s σ k u B v₀ t
      = (∑ w ∈ B.support.erase v₀, (B w : ℝ) * Pr v₀ w)
        - (((k : ℝ) - 2 * (e : ℝ)) * Real.log (⨆ i, ‖σ (evalVec s v₀ i)‖)
            + (e : ℝ) * Real.log (⨆ q : Fin r × Fin r,
                ‖σ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))‖)
            - Real.log ‖σ (regVal s v₀ t k e u)‖) := by
    unfold genFun
    rw [Finsupp.sum, Finsupp.support_erase, heR]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]
  rw [show (fun n => pointFun N s σ k u B (v n)) = fun n => (∑ w ∈ B.support.erase v₀, (B w : ℝ) * Pr (v n) w)
        - ((k : ℝ) * Real.log (⨆ i, ‖σ (evalVec s (v n) i)‖) - Real.log ‖σ (secVal s (v n) k u)‖
            - (e : ℝ) * Pr (v n) v₀) from funext hsplit, hlimit]
  refine Tendsto.sub ?_ hcore
  refine tendsto_finset_sum _ fun w hw => ?_
  exact (hprox w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)).const_mul _

end P2MJA

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.InfinitePlace ↥L),
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (v₀ = cuspInftyBar N ∨
          (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) ∈ v₀.toValuationSubring) →
        ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        |((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            - (((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
              + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m)|
          ≤ c₀ * k := by
  obtain ⟨c₀, h⟩ := P2MJA.jensen_arch_at_of_AT N s hs
    (fun v₀ => v₀ = cuspInftyBar N ∨ (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) ∈ v₀.toValuationSubring)
    (P2MJA.ATShape_of_ws23 N s (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
      (fun v₀ t ht hv₀ => ModularCurve.JZero.exists_seq_tendsto_place N s hs v₀ t ht hv₀))
  refine ⟨c₀, fun k u hu0 hu B hB L _ ν x hx => ?_⟩
  obtain ⟨m, hm⟩ := h k u hu0 hu B hB L ν x hx
  exact ⟨m, fun v₀ hv₀ t ht hx₀ c hc y hy hy0 => hm v₀ t (fun _ => hv₀) ht hx₀ c hc y hy hy0⟩

end S_ModularCurve_JZero_jensen_arch_at_of_nonCuspidal
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_arch_at_of_nonCuspidal (solution)
