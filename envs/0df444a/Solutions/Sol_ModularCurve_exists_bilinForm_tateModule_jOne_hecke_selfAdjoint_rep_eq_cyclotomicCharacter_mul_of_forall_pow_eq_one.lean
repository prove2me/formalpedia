-- Prove2me | solution 1 for ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/4a77c926-321e-5721-9aaf-8adcfd2598fe

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_XH
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_AlgebraicCurve_Pic0_exists_weilPairing
import Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsAll
import Theorems.Thm_ModularCurve_heckeDiamondCommuteBar
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaOneBar
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime"
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_heckeAlphaHBar ModularCurve.coe_heckeBetaHBarOf CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X"
p2m_attr_erase "simp" "ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.qExpandAlgHomC_apply ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicCurve TensorProduct

local notation "Qbar" => AlgebraicClosure ℚ

namespace WeilCycOne

section RootTower

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]

def zeta : ℕ → K
  | 0 => 1
  | 1 => (HasEnoughRootsOfUnity.exists_primitiveRoot K p).choose
  | (k + 2) => (IsAlgClosed.exists_pow_nat_eq (zeta (k + 1)) hp.out.pos).choose

theorem zeta_succ_pow (k : ℕ) : zeta K p (k + 1) ^ p = zeta K p k := by
  match k with
  | 0 =>
    show (HasEnoughRootsOfUnity.exists_primitiveRoot K p).choose ^ p = 1
    exact (HasEnoughRootsOfUnity.exists_primitiveRoot K p).choose_spec.pow_eq_one
  | k + 1 =>
    show (IsAlgClosed.exists_pow_nat_eq (zeta K p (k + 1)) hp.out.pos).choose ^ p = _
    exact (IsAlgClosed.exists_pow_nat_eq (zeta K p (k + 1)) hp.out.pos).choose_spec

theorem isPrimitiveRoot_zeta : ∀ k : ℕ, IsPrimitiveRoot (zeta K p k) (p ^ k)
  | 0 => by
    rw [pow_zero]
    exact IsPrimitiveRoot.one
  | 1 => by
    rw [pow_one]
    exact (HasEnoughRootsOfUnity.exists_primitiveRoot K p).choose_spec
  | k + 2 => by
    have ih := isPrimitiveRoot_zeta (k + 1)
    have hη : zeta K p (k + 2) ^ p = zeta K p (k + 1) := zeta_succ_pow K p (k + 1)
    have hp1 : 1 < p := hp.out.one_lt
    have h1 : zeta K p (k + 2) ^ p ^ (k + 2) = 1 := by
      rw [pow_succ' p (k + 1), pow_mul, hη, ih.pow_eq_one]
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 (orderOf_dvd_of_pow_eq_one h1)
    have hjk : j = k + 2 := by
      by_contra hne
      have hjle : j ≤ k + 1 := by omega
      have h2 : zeta K p (k + 2) ^ p ^ (k + 1) = 1 :=
        orderOf_dvd_iff_pow_eq_one.1 (hj' ▸ pow_dvd_pow p hjle)
      rw [pow_succ' p k, pow_mul, hη] at h2
      have h3 := ih.dvd_of_pow_eq_one _ h2
      rw [Nat.pow_dvd_pow_iff_le_right hp1] at h3
      omega
    have hord : p ^ (k + 2) = orderOf (zeta K p (k + 2)) := by rw [hj', hjk]
    rw [hord]
    exact IsPrimitiveRoot.orderOf (zeta K p (k + 2))

variable {K}

open Classical in

def dlog (k : ℕ) (u : K) : ZMod (p ^ k) :=
  if h : ∃ i : ℕ, zeta K p k ^ i = u then (h.choose : ZMod (p ^ k)) else 0

theorem zeta_pow_dlog_val {k : ℕ} {u : K} (hu : u ^ p ^ k = 1) :
    zeta K p k ^ (dlog p k u).val = u := by
  have h : ∃ i : ℕ, zeta K p k ^ i = u := by
    obtain ⟨i, -, hi⟩ := (isPrimitiveRoot_zeta K p k).eq_pow_of_pow_eq_one hu
    exact ⟨i, hi⟩
  have ho : orderOf (zeta K p k) = p ^ k := (isPrimitiveRoot_zeta K p k).eq_orderOf.symm
  rw [dlog, dif_pos h, ZMod.val_natCast]
  conv_rhs => rw [← h.choose_spec, ← pow_mod_orderOf, ho]

theorem dlog_eq_natCast {k c : ℕ} {u : K} (hc : zeta K p k ^ c = u) : dlog p k u = c := by
  have h : ∃ i : ℕ, zeta K p k ^ i = u := ⟨c, hc⟩
  have hζ := isPrimitiveRoot_zeta K p k
  have ho : orderOf (zeta K p k) = p ^ k := hζ.eq_orderOf.symm
  have hpos : 0 < p ^ k := pow_pos hp.out.pos k
  rw [dlog, dif_pos h, ZMod.natCast_eq_natCast_iff]
  show h.choose % p ^ k = c % p ^ k
  apply hζ.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
  rw [← ho, pow_mod_orderOf, pow_mod_orderOf, h.choose_spec, hc]

theorem dlog_mul {k : ℕ} {u v : K} (hu : u ^ p ^ k = 1) (hv : v ^ p ^ k = 1) :
    dlog p k (u * v) = dlog p k u + dlog p k v := by
  have h := dlog_eq_natCast p (k := k) (u := u * v) (c := (dlog p k u).val + (dlog p k v).val)
    (by rw [pow_add, zeta_pow_dlog_val p hu, zeta_pow_dlog_val p hv])
  rw [h, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem dlog_pow {k : ℕ} {u : K} (hu : u ^ p ^ k = 1) (c : ℕ) :
    dlog p k (u ^ c) = c * dlog p k u := by
  have h := dlog_eq_natCast p (k := k) (u := u ^ c) (c := (dlog p k u).val * c)
    (by rw [pow_mul, zeta_pow_dlog_val p hu])
  rw [h, Nat.cast_mul, ZMod.natCast_zmod_val, mul_comm]

theorem eq_one_of_dlog_eq_zero {k : ℕ} {u : K} (hu : u ^ p ^ k = 1) (h : dlog p k u = 0) :
    u = 1 := by
  rw [← zeta_pow_dlog_val p hu, h, ZMod.val_zero, pow_zero]

theorem natCast_dlog_succ_val {k : ℕ} {u : K} (hu : u ^ p ^ (k + 1) = 1) :
    (((dlog p (k + 1) u).val : ℕ) : ZMod (p ^ k)) = dlog p k (u ^ p) := by
  have h2 : zeta K p k ^ (dlog p (k + 1) u).val = u ^ p := by
    rw [← zeta_succ_pow K p k, ← pow_mul, mul_comm, pow_mul, zeta_pow_dlog_val p hu]
  exact (dlog_eq_natCast p h2).symm

end RootTower

structure LevelPairing (K : Type*) [Field K] (p : ℕ) (J : Type) [AddCommGroup J] where

  e : ℕ → J → J → K
  pow_eq_one : ∀ (k : ℕ) (u v : J), ((p ^ k : ℕ) : ℤ) • u = 0 → ((p ^ k : ℕ) : ℤ) • v = 0 →
    e k u v ^ p ^ k = 1
  add_left : ∀ (k : ℕ) (u u' v : J), ((p ^ k : ℕ) : ℤ) • u = 0 → ((p ^ k : ℕ) : ℤ) • u' = 0 →
    ((p ^ k : ℕ) : ℤ) • v = 0 → e k (u + u') v = e k u v * e k u' v
  add_right : ∀ (k : ℕ) (u v v' : J), ((p ^ k : ℕ) : ℤ) • u = 0 → ((p ^ k : ℕ) : ℤ) • v = 0 →
    ((p ^ k : ℕ) : ℤ) • v' = 0 → e k u (v + v') = e k u v * e k u v'
  compat : ∀ (k : ℕ) (u v : J), ((p ^ (k + 1) : ℕ) : ℤ) • u = 0 →
    ((p ^ (k + 1) : ℕ) : ℤ) • v = 0 →
    e k (((p : ℕ) : ℤ) • u) (((p : ℕ) : ℤ) • v) = e (k + 1) u v ^ p

theorem exists_tateModule_apply_eq {p : ℕ} {J : Type} [AddCommGroup J]
    (hdiv : ∀ u : J, ∃ v : J, ((p : ℕ) : ℤ) • v = u) (k : ℕ) (u : J)
    (hu : ((p ^ k : ℕ) : ℤ) • u = 0) : ∃ x : TateModule p J, (x : ℕ → J) k = u := by
  classical
  choose dv hdv using hdiv
  let next : (k : ℕ) → Submodule.torsionBy ℤ J ((p ^ k : ℕ) : ℤ) →
      Submodule.torsionBy ℤ J ((p ^ (k + 1) : ℕ) : ℤ) :=
    fun k m => ⟨dv m, (Submodule.mem_torsionBy_iff _ _).2 (by
      rw [pow_succ, Nat.cast_mul, mul_smul, hdv]
      exact (Submodule.mem_torsionBy_iff _ _).1 m.2)⟩
  refine ⟨⟨TateModule.liftFun next k ⟨u, (Submodule.mem_torsionBy_iff _ _).2 hu⟩,
    TateModule.liftFun_mem (fun k m => hdv (m : J)) k _⟩, ?_⟩
  change TateModule.liftFun next k ⟨u, _⟩ k = u
  rw [TateModule.liftFun_of_le le_rfl, TateModule.coe_liftAux_congr (Nat.sub_self k)]
  rfl

namespace LevelPairing

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]
  {J : Type} [AddCommGroup J] (E : LevelPairing K p J)

local notation "T" => TateModule p J

omit [IsAlgClosed K] in
theorem e_ne_zero (k : ℕ) (u v : J) (hu : ((p ^ k : ℕ) : ℤ) • u = 0)
    (hv : ((p ^ k : ℕ) : ℤ) • v = 0) : E.e k u v ≠ 0 := by
  intro h0
  have := E.pow_eq_one k u v hu hv
  rw [h0, zero_pow (pow_ne_zero k hp.out.ne_zero)] at this
  exact zero_ne_one this

omit [IsAlgClosed K] in
theorem e_zero_left (k : ℕ) (v : J) (hv : ((p ^ k : ℕ) : ℤ) • v = 0) : E.e k 0 v = 1 := by
  have h := E.add_left k 0 0 v (smul_zero _) (smul_zero _) hv
  rw [add_zero] at h
  exact (mul_eq_left₀ (E.e_ne_zero k 0 v (smul_zero _) hv)).1 h.symm

omit [IsAlgClosed K] in
theorem e_zero_right (k : ℕ) (u : J) (hu : ((p ^ k : ℕ) : ℤ) • u = 0) : E.e k u 0 = 1 := by
  have h := E.add_right k u 0 0 hu (smul_zero _) (smul_zero _)
  rw [add_zero] at h
  exact (mul_eq_left₀ (E.e_ne_zero k u 0 hu (smul_zero _))).1 h.symm

theorem zsmul_torsion {n : ℤ} (c : ℤ) {u : J} (hu : n • u = 0) : n • (c • u) = 0 := by
  rw [smul_comm, hu, smul_zero]

omit [IsAlgClosed K] in
theorem e_natCast_zsmul_left (k : ℕ) (c : ℕ) (u v : J) (hu : ((p ^ k : ℕ) : ℤ) • u = 0)
    (hv : ((p ^ k : ℕ) : ℤ) • v = 0) : E.e k ((c : ℤ) • u) v = E.e k u v ^ c := by
  induction c with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact E.e_zero_left k v hv
  | succ c ih =>
    rw [Nat.cast_succ, add_smul, one_smul, E.add_left k _ _ v (zsmul_torsion _ hu) hu hv, ih,
      pow_succ]

omit [IsAlgClosed K] in
theorem e_natCast_zsmul_right (k : ℕ) (c : ℕ) (u v : J) (hu : ((p ^ k : ℕ) : ℤ) • u = 0)
    (hv : ((p ^ k : ℕ) : ℤ) • v = 0) : E.e k u ((c : ℤ) • v) = E.e k u v ^ c := by
  induction c with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact E.e_zero_right k u hu
  | succ c ih =>
    rw [Nat.cast_succ, add_smul, one_smul, E.add_right k u _ _ hu (zsmul_torsion _ hv) hv, ih,
      pow_succ]

def seq (x y : T) (k : ℕ) : ℤ :=
  ((dlog p k (E.e k ((x : ℕ → J) k) ((y : ℕ → J) k))).val : ℤ)

theorem seq_dvd (x y : T) (i : ℕ) :
    (p : ℤ) ^ i ∣ E.seq x y (i + 1) - E.seq x y i := by
  have htx := TateModule.torsion x (i + 1)
  have hty := TateModule.torsion y (i + 1)
  have h : ((E.seq x y i : ℤ) : ZMod (p ^ i)) = ((E.seq x y (i + 1) : ℤ) : ZMod (p ^ i)) := by
    rw [seq, seq, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      natCast_dlog_succ_val p (E.pow_eq_one _ _ _ htx hty), ← E.compat i _ _ htx hty,
      TateModule.compat x i, TateModule.compat y i]
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
  simpa using this

def pair (x y : T) : ℤ_[p] :=
  PadicInt.ofIntSeq (E.seq x y) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (E.seq_dvd x y))

theorem toZModPow_pair (x y : T) (k : ℕ) :
    PadicInt.toZModPow k (E.pair x y) = dlog p k (E.e k ((x : ℕ → J) k) ((y : ℕ → J) k)) := by
  rw [pair, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (E.seq_dvd x y), seq, Int.cast_natCast,
    ZMod.natCast_zmod_val]

omit [IsAlgClosed K] [CharZero K] hp in
theorem e_pow_eq_one (x y : T) (k : ℕ) :
    E.e k ((x : ℕ → J) k) ((y : ℕ → J) k) ^ p ^ k = 1 :=
  E.pow_eq_one k _ _ (TateModule.torsion x k) (TateModule.torsion y k)

theorem pair_add_left (x x' y : T) :
    E.pair (x + x') y = E.pair x y + E.pair x' y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_add, toZModPow_pair, toZModPow_pair, toZModPow_pair, TateModule.coe_add,
    Pi.add_apply, E.add_left k _ _ _ (TateModule.torsion x k) (TateModule.torsion x' k)
      (TateModule.torsion y k), dlog_mul p (E.e_pow_eq_one x y k) (E.e_pow_eq_one x' y k)]

theorem pair_add_right (x y y' : T) :
    E.pair x (y + y') = E.pair x y + E.pair x y' := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_add, toZModPow_pair, toZModPow_pair, toZModPow_pair, TateModule.coe_add,
    Pi.add_apply, E.add_right k _ _ _ (TateModule.torsion x k) (TateModule.torsion y k)
      (TateModule.torsion y' k), dlog_mul p (E.e_pow_eq_one x y k) (E.e_pow_eq_one x y' k)]

theorem pair_smul_left (a : ℤ_[p]) (x y : T) :
    E.pair (a • x) y = a * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, toZModPow_pair, toZModPow_pair, TateModule.smul_apply,
    E.e_natCast_zsmul_left k _ _ _ (TateModule.torsion x k) (TateModule.torsion y k),
    dlog_pow p (E.e_pow_eq_one x y k), TateModule.toZModPow_eq_appr]

theorem pair_smul_right (a : ℤ_[p]) (x y : T) :
    E.pair x (a • y) = a * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, toZModPow_pair, toZModPow_pair, TateModule.smul_apply,
    E.e_natCast_zsmul_right k _ _ _ (TateModule.torsion x k) (TateModule.torsion y k),
    dlog_pow p (E.e_pow_eq_one x y k), TateModule.toZModPow_eq_appr]

def pairing : LinearMap.BilinForm ℤ_[p] T :=
  LinearMap.mk₂ ℤ_[p] E.pair E.pair_add_left
    (fun a x y => by rw [E.pair_smul_left, smul_eq_mul]) E.pair_add_right
    (fun a x y => by rw [E.pair_smul_right, smul_eq_mul])

@[scoped simp] theorem pairing_apply (x y : T) : E.pairing x y = E.pair x y := rfl

theorem pair_eq_of_forall {x y x' y' : T}
    (h : ∀ k, E.e k ((x' : ℕ → J) k) ((y' : ℕ → J) k) = E.e k ((x : ℕ → J) k) ((y : ℕ → J) k)) :
    E.pair x' y' = E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [toZModPow_pair, toZModPow_pair, h k]

theorem pair_eq_cyc_mul [∀ i : ℕ, HasEnoughRootsOfUnity K (p ^ i)] (τ : K ≃+* K) {x y x' y' : T}
    (h : ∀ k, E.e k ((x' : ℕ → J) k) ((y' : ℕ → J) k) = τ (E.e k ((x : ℕ → J) k) ((y : ℕ → J) k))) :
    E.pair x' y' = ((cyclotomicCharacter K p τ : ℤ_[p]ˣ) : ℤ_[p]) * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, toZModPow_pair, toZModPow_pair, h k,
    cyclotomicCharacter.spec p τ _ (E.e_pow_eq_one x y k), dlog_pow p (E.e_pow_eq_one x y k),
    ZMod.natCast_zmod_val]

theorem pair_nondeg_left (hdiv : ∀ u : J, ∃ v : J, ((p : ℕ) : ℤ) • v = u)
    (hnd : ∀ (k : ℕ) (u : J), ((p ^ k : ℕ) : ℤ) • u = 0 →
      (∀ v : J, ((p ^ k : ℕ) : ℤ) • v = 0 → E.e k u v = 1) → u = 0)
    (x : T) (hx : ∀ y, E.pair x y = 0) : x = 0 := by
  refine Subtype.ext (funext fun k => ?_)
  rw [TateModule.coe_zero, Pi.zero_apply]
  refine hnd k _ (TateModule.torsion x k) fun v hv => ?_
  obtain ⟨y, hy⟩ := exists_tateModule_apply_eq hdiv k v hv
  have h := congrArg (PadicInt.toZModPow k) (hx y)
  rw [toZModPow_pair, map_zero, hy] at h
  exact eq_one_of_dlog_eq_zero p (E.pow_eq_one k _ _ (TateModule.torsion x k) hv) h

end LevelPairing
p2m_reactivate "P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.WeilCycOne.LevelPairing"

section BC

variable {R : Type*} [CommRing R] {T : Type*} [AddCommGroup T] [Module R T]
variable (K : Type*) [Field K] [Algebra R K]

def BV (P : LinearMap.BilinForm R T) : LinearMap.BilinForm K (K ⊗[R] T) := P.baseChange K

theorem BV_tmul (P : LinearMap.BilinForm R T) (c c' : K) (x y : T) :
    BV K P (c ⊗ₜ x) (c' ⊗ₜ y) = (P x y) • (c * c') := rfl

theorem tmul_eq_smul_one_tmul (c : K) (x : T) :
    c ⊗ₜ[R] x = c • ((1 : K) ⊗ₜ[R] x) := by
  rw [smul_tmul', smul_eq_mul, mul_one]

theorem BV_adjoint (P : LinearMap.BilinForm R T) (φ φ' : T →ₗ[R] T)
    (h : ∀ x y, P (φ x) y = P x (φ' y)) (v w : K ⊗[R] T) :
    BV K P (φ.baseChange K v) w = BV K P v (φ'.baseChange K w) := by
  induction v using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  | tmul c x =>
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul c' y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, BV_tmul, BV_tmul, h]
    | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']
  | add v v' hv hv' =>
    rw [map_add, map_add, LinearMap.add_apply, hv, hv', map_add, LinearMap.add_apply]

theorem BV_scale (P : LinearMap.BilinForm R T) (φ : T →ₗ[R] T) (r : R)
    (h : ∀ x y, P (φ x) (φ y) = r * P x y) (v w : K ⊗[R] T) :
    BV K P (φ.baseChange K v) (φ.baseChange K w) = algebraMap R K r * BV K P v w := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, mul_zero]
  | tmul c x =>
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul c' y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, BV_tmul, BV_tmul, h,
        Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
    | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', mul_add]
  | add v v' hv hv' =>
    rw [map_add, map_add, LinearMap.add_apply, hv, hv', map_add, LinearMap.add_apply, mul_add]

theorem BV_separating {ι : Type*} [Fintype ι] [DecidableEq ι] [IsDomain R]
    (P : LinearMap.BilinForm R T) (b : Module.Basis ι R T)
    (hinj : Function.Injective (algebraMap R K))
    (hP : ∀ x, (∀ y, P x y = 0) → x = 0) :
    (∀ w, (∀ v, BV K P v w = 0) → w = 0) ∧ (∀ v, (∀ w, BV K P v w = 0) → v = 0) := by
  set ψ : R →+* K := algebraMap R K with hψ

  set G : Matrix ι ι R := Matrix.of fun i j => P (b i) (b j) with hG
  have hGij : ∀ i j, G i j = P (b i) (b j) := fun i j => rfl
  have hPx : ∀ (c : ι → R) (j : ι), P (b.equivFun.symm c) (b j) = ∑ i, c i * G i j := by
    intro c j
    rw [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hGij]
  have hdet : G.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    have hx : b.equivFun.symm c = 0 := by
      refine hP _ fun y => ?_
      rw [← b.sum_equivFun y, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, hPx]
      have hj : (∑ i, c i * G i j) = Matrix.vecMul c G j := rfl
      rw [hj, hc, Pi.zero_apply, smul_zero]
    exact hc0 (b.equivFun.symm.injective (by rw [hx, map_zero]))
  have hdetK : (G.map ψ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero_iff ψ hinj).mpr hdet

  let bK : Module.Basis ι K (K ⊗[R] T) := Algebra.TensorProduct.basis K b
  have hbK : ∀ i, bK i = (1 : K) ⊗ₜ b i := by
    intro i
    simp only [bK, Algebra.TensorProduct.basis_apply]
  have hGram : ∀ i j, BV K P (bK i) (bK j) = ψ (G i j) := by
    intro i j
    rw [hbK, hbK, BV_tmul, mul_one, hGij, hψ, Algebra.algebraMap_eq_smul_one]
  have hleft : ∀ (v : K ⊗[R] T) (j : ι),
      BV K P v (bK j) = ∑ i, bK.equivFun v i * (G.map ψ) i j := by
    intro v j
    conv_lhs => rw [← bK.sum_equivFun v]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, hGram, smul_eq_mul, Matrix.map_apply]
  have hright : ∀ (i : ι) (w : K ⊗[R] T),
      BV K P (bK i) w = ∑ j, (G.map ψ) i j * bK.equivFun w j := by
    intro i w
    conv_lhs => rw [← bK.sum_equivFun w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hGram, smul_eq_mul, mul_comm, Matrix.map_apply]
  refine ⟨fun w hw => ?_, fun v hv => ?_⟩
  · have hd : Matrix.mulVec (G.map ψ) (bK.equivFun w) = 0 := by
      funext i
      have := hw (bK i)
      rw [hright] at this
      exact this
    by_contra hne
    have hd0 : bK.equivFun w ≠ 0 := fun h0 => hne (bK.equivFun.injective (by rw [h0, map_zero]))
    exact hdetK (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hd0, hd⟩)
  · have hc : Matrix.vecMul (bK.equivFun v) (G.map ψ) = 0 := by
      funext j
      have := hv (bK j)
      rw [hleft] at this
      exact this
    by_contra hne
    have hc0 : bK.equivFun v ≠ 0 := fun h0 => hne (bK.equivFun.injective (by rw [h0, map_zero]))
    exact hdetK (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hc0, hc⟩)

theorem mem_span_one_tmul (v : K ⊗[R] T) :
    v ∈ Submodule.span K ((fun x : T => (1 : K) ⊗ₜ[R] x) '' Set.univ) := by
  induction v using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul c x =>
    rw [tmul_eq_smul_one_tmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, Set.mem_univ _, rfl⟩)
  | add v w hv hw => exact Submodule.add_mem _ hv hw

end BC
p2m_reactivate "P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.WeilCycOne.LevelPairing"

theorem padicInt_ringHom_injective {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharZero K]
    (f : ℤ_[p] →+* K) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra hne
  rw [PadicInt.unitCoeff_spec hne, map_mul, map_pow, map_natCast, mul_eq_zero] at hx
  rcases hx with h1 | h2
  · exact ((Units.isUnit _).map f).ne_zero h1
  · exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h2

section Modular

open ModularCurve CongruenceSubgroup

variable (M : ℕ) [NeZero M]

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  rw [← GammaH_bot]; exact translation_mem_GammaH M ⊥

theorem exists_transcendental_x1FunctionFieldBar :
    ∃ x : x1FunctionFieldBar M, Transcendental Qbar x ∧
      FiniteDimensional (IntermediateField.adjoin Qbar ({x} : Set (x1FunctionFieldBar M)))
        (x1FunctionFieldBar M) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange Qbar (Gamma1 M)
    (T_mem_Gamma1 M)

theorem isCurveOver_x1FunctionFieldBar : IsCurveOver Qbar (x1FunctionFieldBar M) := by
  obtain ⟨x, hx, hfin⟩ := exists_transcendental_x1FunctionFieldBar M
  haveI := hfin
  haveI : PerfectField (IntermediateField.adjoin Qbar ({x} : Set (x1FunctionFieldBar M))) :=
    PerfectField.ofCharZero
  exact AlgebraicCurve.isCurveOver_of_transcendental hx hfin
    Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem transposeInputs (ℓ : Nat.Primes) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∃ (_ : HeckeBetaOneDefined M ℓ) (hα : HeckeAlphaOneBarIntegral Qbar M ℓ)
      (hβ : HeckeBetaOneBarIntegral Qbar M ℓ)
      (_ : HasPrincipalDivisors Qbar (laurentBaseChange Qbar (x1x0FunctionFieldC ℚ M (M * ℓ))))
      (hfinα : FiniteAlong Qbar (heckeAlphaOneBar Qbar M ℓ))
      (hfinβ : FiniteAlong Qbar (heckeBetaOneBar Qbar M ℓ)),
      FundamentalIdentityAlong Qbar (heckeBetaOneBar Qbar M ℓ) hβ ∧
      NormFormulaAlong Qbar (heckeAlphaOneBar Qbar M ℓ) hfinα ∧
      FundamentalIdentityAlong Qbar (heckeAlphaOneBar Qbar M ℓ) hα ∧
      NormFormulaAlong Qbar (heckeBetaOneBar Qbar M ℓ) hfinβ := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  obtain ⟨h0, hα, hβ, hPD, hfinα, hFIβ, hNα⟩ := (ModularCurve.heckeDiamondInputsAll M).1 ℓ
  haveI := hPD
  have hsepα := AlgebraicCurve.separableAlong_of_charZero (heckeAlphaOneBar Qbar M ℓ) hα
  have hsepβ := AlgebraicCurve.separableAlong_of_charZero (heckeBetaOneBar Qbar M ℓ) hβ
  have hFIα := AlgebraicCurve.fundamentalIdentityAlong (heckeAlphaOneBar Qbar M ℓ) hα hfinα hsepα
  have hfinβ : FiniteAlong Qbar (heckeBetaOneBar Qbar M ℓ) := by
    have hr := ModularCurve.finrankAlong_heckeBetaOneBar Qbar M ℓ h0
    have hpos : 0 < AlgebraicCurve.finrankAlong Qbar (heckeBetaOneBar Qbar M ℓ) := by
      rw [hr]; split_ifs
      · exact ℓ.2.pos
      · exact Nat.succ_pos _
    letI := algebraAlong (heckeBetaOneBar Qbar M ℓ)
    exact Module.finite_of_finrank_pos hpos
  have hNβ := AlgebraicCurve.normFormulaAlong (heckeBetaOneBar Qbar M ℓ) hfinβ hsepβ
  exact ⟨h0, hα, hβ, hPD, hfinα, hfinβ, hFIβ, hNα, hFIα, hNβ⟩

theorem exists_pairing (p : ℕ) [hp : Fact p.Prime] :
    ∃ P : LinearMap.BilinForm ℤ_[p] (TateModule p (JOne M)),
      (∀ x, (∀ y, P x y = 0) → x = 0) ∧
      (∀ (φ : JOne M → JOne M),
        ((∃ ℓ : Nat.Primes, φ = heckeOperatorOneBar M ℓ) ∨ (∃ d : ℕ, φ = diamondOneBar M d)) →
        ∀ (x y x' y' : TateModule p (JOne M)),
        (∀ k, (x' : ℕ → JOne M) k = φ ((x : ℕ → JOne M) k)) →
        (∀ k, (y' : ℕ → JOne M) k = φ ((y : ℕ → JOne M) k)) →
        P x' y = P x y') ∧
      (∀ τ : Qbar ≃ₐ[ℚ] Qbar, (∀ ζ : Qbar, ζ ^ M = 1 → τ ζ = ζ) →
        ∀ (x y : TateModule p (JOne M)),
        P (TateModule.rep p (JOne M) (Qbar ≃ₐ[ℚ] Qbar) τ x)
            (TateModule.rep p (JOne M) (Qbar ≃ₐ[ℚ] Qbar) τ y) =
          ((cyclotomicCharacter Qbar p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * P x y) := by
  haveI := isCurveOver_x1FunctionFieldBar M
  have hfg := exists_transcendental_x1FunctionFieldBar M
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  have hpk : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp.out.pos k

  obtain ⟨e, he1, he2, he3, he4, -, he6, he7, he8⟩ :=
    AlgebraicCurve.Pic0.exists_weilPairing.{0, 0, 0} Qbar (x1FunctionFieldBar M) hfg

  obtain ⟨σw, hw1, hw2, hw3, hw4⟩ := ModularCurve.exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul M
  set W : SemilinearAut Qbar (x1FunctionFieldBar M) := SemilinearAut.ofAlgAut σw with hW
  have hWt : ∀ (g : SemilinearAut Qbar (x1FunctionFieldBar M)) {m : ℤ} {v : JOne M},
      m • v = 0 → m • (g • v) = 0 := fun g {m v} hv => by
    rw [← SemilinearAut.smul_zsmul, hv]; exact smul_zero (A := JOne M) g

  have hone : ∀ z : JOne M, diamondOneBar M 1 z = z := by
    intro z
    have h := hw4 1 1 (Nat.coprime_one_left M) (fun ζ _ => by rw [pow_one, AlgEquiv.one_apply])
      (W • z)
    rw [one_smul, one_smul, hw3] at h
    exact h.symm

  have hwσ : ∀ τ : Qbar ≃ₐ[ℚ] Qbar, (∀ ζ : Qbar, ζ ^ M = 1 → τ ζ = ζ) → ∀ z : JOne M,
      W • (τ • z) = τ • (W • z) := by
    intro τ hτ z
    have h := hw4 τ 1 (Nat.coprime_one_left M) (fun ζ hζ => by rw [pow_one, hτ ζ hζ]) z
    rw [hone] at h
    exact h

  let E : LevelPairing Qbar p (JOne M) :=
    { e := fun k u v => e (p ^ k) u (W • v)
      pow_eq_one := fun k u v hu hv => he1 _ _ _ (hpk k) hu (hWt W hv)
      add_left := fun k u u' v hu hu' hv => he2 _ _ _ _ (hpk k) hu hu' (hWt W hv)
      add_right := fun k u v v' hu hv hv' => by
        show e (p ^ k) u (W • (v + v')) = _
        rw [smul_add]; exact he3 _ _ _ _ (hpk k) hu (hWt W hv) (hWt W hv')
      compat := fun k u v hu hv => by
        show e (p ^ k) _ (W • _) = e (p ^ (k + 1)) u (W • v) ^ p
        rw [SemilinearAut.smul_zsmul, pow_succ p k]
        rw [pow_succ p k] at hu hv
        exact he6 (p ^ k) p u (W • v) (hpk k) hp.out.pos hu (hWt W hv) }
  have hE : ∀ k u v, E.e k u v = e (p ^ k) u (W • v) := fun _ _ _ => rfl

  have hndL : ∀ (k : ℕ) (u : JOne M), ((p ^ k : ℕ) : ℤ) • u = 0 →
      (∀ v, ((p ^ k : ℕ) : ℤ) • v = 0 → E.e k u v = 1) → u = 0 := fun k u hu h =>
    he4 _ u (hpk k) hu fun y hy => by
      have := h (W⁻¹ • y) (hWt W⁻¹ hy)
      rwa [hE, smul_inv_smul] at this

  have hdiv : ∀ u : JOne M, ∃ v : JOne M, ((p : ℕ) : ℤ) • v = u := fun u => by
    obtain ⟨v, hv⟩ := AlgebraicCurve.Pic0.exists_nsmul_eq Qbar (x1FunctionFieldBar M) hfg p
      hp.out.ne_zero u
    exact ⟨v, by rw [natCast_zsmul, hv]⟩

  have hgen : ∀ (ℓ : Nat.Primes) (n : ℕ) (u v : JOne M), 0 < n → (n : ℤ) • u = 0 →
      (n : ℤ) • v = 0 →
        e n (heckeOperatorOneBar M ℓ u) (W • v) = e n u (W • heckeOperatorOneBar M ℓ v) := by
    intro ℓ n u v hn hu hv
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
    obtain ⟨h0, hα, hβ, hPD, hfinα, hfinβ, hFIβ, hNα, hFIα, hNβ⟩ := transposeInputs M ℓ
    haveI := hPD
    rw [heckeOperatorOneBar_apply, heckeOperatorOneBar_apply,
      heckeOperatorOneAlong_eq h0 hα hβ hFIβ hfinα hNα]
    have h8 := he8 (laurentBaseChange Qbar (x1x0FunctionFieldC ℚ M (M * ℓ)))
      (heckeBetaOneBar Qbar M ℓ) (heckeAlphaOneBar Qbar M ℓ)
      hβ hα hFIβ hfinα hNα hFIα hfinβ hNβ n u (W • v) hn hu (hWt W hv)
    have h2b := hw1 ℓ hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ v
    exact h8.trans (congrArg (e n u) h2b)

  have hdia : ∀ (d : ℕ) (n : ℕ) (u v : JOne M), 0 < n → (n : ℤ) • u = 0 → (n : ℤ) • v = 0 →
      e n (diamondOneBar M d u) (W • v) = e n u (W • diamondOneBar M d v) := by
    intro d n u v hn hu hv
    set D : SemilinearAut Qbar (x1FunctionFieldBar M) := SemilinearAut.ofAlgAut (diamondAutBar M d)
      with hD
    have hDu : ∀ z : JOne M, diamondOneBar M d z = D • z := fun z => rfl
    have h2 : W • (D • v) = D⁻¹ • (W • v) := by
      rw [eq_inv_smul_iff]
      have := hw2 d v
      rwa [hDu, hDu] at this
    rw [hDu, hDu, h2]
    have h7 := he7 n D u (D⁻¹ • (W • v)) hn hu (hWt _ (hWt _ hv))
    rw [smul_inv_smul] at h7
    rw [h7, hD, SemilinearAut.baseAut_ofAlgAut]
    rfl
  refine ⟨E.pairing, fun x hx => E.pair_nondeg_left hdiv hndL x hx, ?_, ?_⟩
  ·
    intro φ hφ x y x' y' hx' hy'
    show E.pair x' y = E.pair x y'
    refine PadicInt.ext_of_toZModPow.1 fun k => ?_
    rw [E.toZModPow_pair, E.toZModPow_pair, hx', hy', hE, hE]
    rcases hφ with ⟨ℓ, rfl⟩ | ⟨d, rfl⟩
    · exact congrArg _ (hgen ℓ (p ^ k) _ _ (hpk k) (TateModule.torsion x k) (TateModule.torsion y k))
    · exact congrArg _ (hdia d (p ^ k) _ _ (hpk k) (TateModule.torsion x k) (TateModule.torsion y k))
  ·
    intro τ hτ x y
    show E.pair _ _ = _ * E.pair x y
    refine E.pair_eq_cyc_mul τ.toRingEquiv (fun k => ?_)
    rw [TateModule.rep_apply, TateModule.rep_apply, hE, hE, hwσ τ hτ,
      galois_smul_pic0_def, galois_smul_pic0_def,
      he7 (p ^ k) _ _ (W • _) (hpk k) (TateModule.torsion x k) (hWt W (TateModule.torsion y k)),
      baseAut_arithmeticGalois]

end Modular
p2m_reactivate "P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.WeilCycOne.LevelPairing"

section Supply

open ModularCurve

variable {p : ℕ} [Fact p.Prime] {J : Type} [AddCommGroup J]

theorem noZeroSMulDivisors_tateModule : NoZeroSMulDivisors ℤ_[p] (TateModule p J) := by
  refine ⟨fun {a x} h => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    rw [PadicInt.unitCoeff_spec ha] at h
    have h' : ((p : ℤ_[p]) ^ (a.valuation) • x : TateModule p J) = 0 := by
      have := congrArg (fun z => (((PadicInt.unitCoeff ha)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • z) h
      simp only [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, smul_zero] at this
      exact this
    set v := a.valuation
    refine Subtype.ext (funext fun n => ?_)
    have hn := congrArg (fun z : TateModule p J => (z : ℕ → J) (n + v)) h'
    beta_reduce at hn
    rw [TateModule.coe_zero, Pi.zero_apply, ← Nat.cast_pow,
      TateModule.natCast_padicInt_smul_apply, TateModule.compat_pow] at hn
    rw [hn, TateModule.coe_zero, Pi.zero_apply]

variable [Module HeckeAlgOne J]

theorem selfAdjoint_all (P : LinearMap.BilinForm ℤ_[p] (TateModule p J))
    (hX : ∀ (i : Nat.Primes ⊕ ℕ) (x y : TateModule p J),
      P (tateHeckeRepOne p J (MvPolynomial.X i) x) y = P x (tateHeckeRepOne p J (MvPolynomial.X i) y))
    (t : HeckeAlgOne) (x y : TateModule p J) :
    P (tateHeckeRepOne p J t x) y = P x (tateHeckeRepOne p J t y) := by
  set R := tateHeckeRepOne p J with hR
  induction t using MvPolynomial.induction_on generalizing x y with
  | C a =>
    have hC : ∀ z : TateModule p J, R (MvPolynomial.C a) z = a • z := by
      intro z
      refine Subtype.ext (funext fun n => ?_)
      rw [coe_tateHeckeRepOne_apply_apply, heckeModuleOneBar_C_smul_generic]
      rfl
    rw [hC, hC, map_zsmul, LinearMap.smul_apply, map_zsmul]
  | add s t hs ht =>
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, LinearMap.add_apply, hs, ht,
      map_add]
  | mul_X q i hq =>
    rw [map_mul, Module.End.mul_apply, hq, hX, ← Module.End.mul_apply, ← map_mul, mul_comm,
      map_mul, Module.End.mul_apply]
where

  heckeModuleOneBar_C_smul_generic (a : ℤ) (z : J) : (MvPolynomial.C a : HeckeAlgOne) • z = a • z := by
    rw [← MvPolynomial.algebraMap_eq, eq_intCast, Int.cast_smul_eq_zsmul]

end Supply
p2m_reactivate "P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.WeilCycOne.LevelPairing"

end WeilCycOne
p2m_reactivate "P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.WeilCycOne.LevelPairing P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.WeilCycOne"

open ModularCurve WeilCycOne CongruenceSubgroup in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ B : LinearMap.BilinForm K (K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) ∧
      (∀ (t : ModularCurve.HeckeAlgOne) (v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
        B ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K v) w =
          B v ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K w)) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ) →
        ∀ v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M),
          B ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange
                K v)
            ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange
                K w) =
            algebraMap ℤ_[p] K
                ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * B v w := by
  classical
  letI := ModularCurve.heckeModuleOneBar M
  have hp : Fact p.Prime := inferInstance
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  let T := TateModule p (JOne M)

  have hPex := exists_pairing M p
  let PT : LinearMap.BilinForm ℤ_[p] T := hPex.choose
  have hPnd : ∀ x, (∀ y, PT x y = 0) → x = 0 := hPex.choose_spec.1
  have hPop := hPex.choose_spec.2.1
  have hPgal := hPex.choose_spec.2.2

  let B : LinearMap.BilinForm K (K ⊗[ℤ_[p]] T) := BV K PT

  have hinj : Function.Injective (algebraMap ℤ_[p] K) := padicInt_ringHom_injective _
  haveI : Module.Finite ℤ_[p] T := ModularCurve.moduleFinite_padicInt_tateModule_jOne M p
  haveI : NoZeroSMulDivisors ℤ_[p] T := noZeroSMulDivisors_tateModule
  haveI : Module.Free ℤ_[p] T := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ_[p] T
  have hsep := BV_separating K PT b hinj hPnd
  refine ⟨B, hsep.2, hsep.1, ?_, ?_⟩
  ·
    intro t v w
    have hcomm := ModularCurve.heckeDiamondCommuteBar M
    have hX : ∀ (i : Nat.Primes ⊕ ℕ) (x y : T),
        PT (tateHeckeRepOne p (JOne M) (MvPolynomial.X i) x) y =
          PT x (tateHeckeRepOne p (JOne M) (MvPolynomial.X i) y) := by
      intro i x y
      have hlev : ∀ z : T, ∀ k, ((tateHeckeRepOne p (JOne M) (MvPolynomial.X i) z : T) : ℕ → JOne M) k
          = heckeDiamondGenBar M i ((z : ℕ → JOne M) k) := fun z k => by
        rw [coe_tateHeckeRepOne_apply_apply, heckeModuleOneBar_smul_def hcomm, heckeEvalOneBar_X]
      refine hPop (heckeDiamondGenBar M i) ?_ x y _ _ (hlev x) (hlev y)
      rcases i with ℓ | d
      · exact Or.inl ⟨ℓ, rfl⟩
      · exact Or.inr ⟨d, rfl⟩
    exact BV_adjoint K PT _ _ (selfAdjoint_all PT hX t) v w
  ·
    intro σ hσ v w
    exact BV_scale K PT _ _ (hPgal σ hσ) v w

end
end S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one
end P2MW
export P2MW.S_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one (solution)
