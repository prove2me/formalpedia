-- Prove2me | solution 1 for ModularCurve.exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/36f16a98-9b3f-57bc-9a82-19ec2568eab9

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul
import Theorems.Thm_AlgebraicCurve_Pic0_exists_antisymmWeilPairing
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental
import Theorems.Thm_AlgebraicCurve_separableAlong_of_charZero
import Theorems.Thm_AlgebraicCurve_fundamentalIdentityAlong
import Theorems.Thm_AlgebraicCurve_normFormulaAlong
import Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one
import Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk"
p2m_attr_erase "simp" "AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace SimilitudeEngineH

section RootTower

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]

noncomputable def zeta : ℕ → K
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

noncomputable def dlog (k : ℕ) (u : K) : ZMod (p ^ k) :=
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

omit [IsAlgClosed K] in

theorem e_zsmul_left_eq_right (k : ℕ) (a : ℤ) (u v : J) (hu : ((p ^ k : ℕ) : ℤ) • u = 0)
    (hv : ((p ^ k : ℕ) : ℤ) • v = 0) : E.e k (a • u) v = E.e k u (a • v) := by

  have hpk : (0 : ℤ) < ((p ^ k : ℕ) : ℤ) := by exact_mod_cast pow_pos hp.out.pos k
  set b : ℕ := (a % ((p ^ k : ℕ) : ℤ)).toNat with hb
  have hb' : (b : ℤ) = a % ((p ^ k : ℕ) : ℤ) := by
    rw [hb, Int.toNat_of_nonneg (Int.emod_nonneg _ hpk.ne')]
  have hred : ∀ w : J, ((p ^ k : ℕ) : ℤ) • w = 0 → a • w = (b : ℤ) • w := by
    intro w hw
    conv_lhs => rw [← Int.mul_ediv_add_emod a ((p ^ k : ℕ) : ℤ)]
    rw [add_smul, mul_comm, mul_smul, hw, smul_zero, zero_add, hb']
  rw [hred u hu, hred v hv, E.e_natCast_zsmul_left k b u v hu hv,
    E.e_natCast_zsmul_right k b u v hu hv]

noncomputable def seq (x y : TateModule p J) (k : ℕ) : ℤ :=
  ((dlog p k (E.e k ((x : ℕ → J) k) ((y : ℕ → J) k))).val : ℤ)

theorem seq_dvd (x y : TateModule p J) (i : ℕ) :
    (p : ℤ) ^ i ∣ E.seq x y (i + 1) - E.seq x y i := by
  have htx := TateModule.torsion x (i + 1)
  have hty := TateModule.torsion y (i + 1)
  have h : ((E.seq x y i : ℤ) : ZMod (p ^ i)) = ((E.seq x y (i + 1) : ℤ) : ZMod (p ^ i)) := by
    rw [seq, seq, Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val,
      natCast_dlog_succ_val p (E.pow_eq_one _ _ _ htx hty), ← E.compat i _ _ htx hty,
      TateModule.compat x i, TateModule.compat y i]
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
  simpa using this

noncomputable def pair (x y : TateModule p J) : ℤ_[p] :=
  PadicInt.ofIntSeq (E.seq x y) (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (E.seq_dvd x y))

theorem toZModPow_pair (x y : TateModule p J) (k : ℕ) :
    PadicInt.toZModPow k (E.pair x y) = dlog p k (E.e k ((x : ℕ → J) k) ((y : ℕ → J) k)) := by
  rw [pair, PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ p (E.seq_dvd x y), seq, Int.cast_natCast,
    ZMod.natCast_zmod_val]

omit [IsAlgClosed K] [CharZero K] hp in
theorem e_pow_eq_one (x y : TateModule p J) (k : ℕ) :
    E.e k ((x : ℕ → J) k) ((y : ℕ → J) k) ^ p ^ k = 1 :=
  E.pow_eq_one k _ _ (TateModule.torsion x k) (TateModule.torsion y k)

theorem pair_add_left (x x' y : TateModule p J) :
    E.pair (x + x') y = E.pair x y + E.pair x' y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_add, toZModPow_pair, toZModPow_pair, toZModPow_pair, TateModule.coe_add,
    Pi.add_apply, E.add_left k _ _ _ (TateModule.torsion x k) (TateModule.torsion x' k)
      (TateModule.torsion y k), dlog_mul p (E.e_pow_eq_one x y k) (E.e_pow_eq_one x' y k)]

theorem pair_add_right (x y y' : TateModule p J) :
    E.pair x (y + y') = E.pair x y + E.pair x y' := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_add, toZModPow_pair, toZModPow_pair, toZModPow_pair, TateModule.coe_add,
    Pi.add_apply, E.add_right k _ _ _ (TateModule.torsion x k) (TateModule.torsion y k)
      (TateModule.torsion y' k), dlog_mul p (E.e_pow_eq_one x y k) (E.e_pow_eq_one x y' k)]

theorem pair_smul_left (a : ℤ_[p]) (x y : TateModule p J) :
    E.pair (a • x) y = a * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, toZModPow_pair, toZModPow_pair, TateModule.smul_apply,
    E.e_natCast_zsmul_left k _ _ _ (TateModule.torsion x k) (TateModule.torsion y k),
    dlog_pow p (E.e_pow_eq_one x y k), TateModule.toZModPow_eq_appr]

theorem pair_smul_right (a : ℤ_[p]) (x y : TateModule p J) :
    E.pair x (a • y) = a * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, toZModPow_pair, toZModPow_pair, TateModule.smul_apply,
    E.e_natCast_zsmul_right k _ _ _ (TateModule.torsion x k) (TateModule.torsion y k),
    dlog_pow p (E.e_pow_eq_one x y k), TateModule.toZModPow_eq_appr]

noncomputable def pairing : TateModule p J →ₗ[ℤ_[p]] TateModule p J →ₗ[ℤ_[p]] ℤ_[p] :=
  LinearMap.mk₂ ℤ_[p] E.pair E.pair_add_left
    (fun a x y => by rw [E.pair_smul_left, smul_eq_mul]) E.pair_add_right
    (fun a x y => by rw [E.pair_smul_right, smul_eq_mul])

@[scoped simp] theorem pairing_apply (x y : TateModule p J) : E.pairing x y = E.pair x y := rfl

theorem pair_eq_natCast_mul {x y x' y' : TateModule p J} {q : ℕ}
    (h : ∀ k, E.e k ((x' : ℕ → J) k) ((y' : ℕ → J) k)
      = E.e k ((x : ℕ → J) k) ((y : ℕ → J) k) ^ q) :
    E.pair x' y' = (q : ℤ_[p]) * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, map_natCast, toZModPow_pair, toZModPow_pair, h k,
    dlog_pow p (E.e_pow_eq_one x y k)]

theorem pair_eq_mul_of_toZModPow {x y x' y' : TateModule p J} {u : ℤ_[p]}
    (h : ∀ k, E.e k ((x' : ℕ → J) k) ((y' : ℕ → J) k)
      = E.e k ((x : ℕ → J) k) ((y : ℕ → J) k) ^ (PadicInt.toZModPow k u).val) :
    E.pair x' y' = u * E.pair x y := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [map_mul, toZModPow_pair, toZModPow_pair, h k, dlog_pow p (E.e_pow_eq_one x y k),
    ZMod.natCast_zmod_val]

theorem pair_eq_of_forall {x y x' y' : TateModule p J}
    (h : ∀ k, E.e k ((x' : ℕ → J) k) ((y' : ℕ → J) k) = E.e k ((x : ℕ → J) k) ((y : ℕ → J) k)) :
    E.pair x' y' = E.pair x y := by
  have := E.pair_eq_natCast_mul (q := 1) (x := x) (y := y) (x' := x') (y' := y')
    (fun k => by rw [pow_one]; exact h k)
  rwa [Nat.cast_one, one_mul] at this

theorem pair_nondeg_left (hdiv : ∀ u : J, ∃ v : J, ((p : ℕ) : ℤ) • v = u)
    (hnd : ∀ (k : ℕ) (u : J), ((p ^ k : ℕ) : ℤ) • u = 0 →
      (∀ v : J, ((p ^ k : ℕ) : ℤ) • v = 0 → E.e k u v = 1) → u = 0)
    (x : TateModule p J) (hx : ∀ y, E.pair x y = 0) : x = 0 := by
  refine Subtype.ext (funext fun k => ?_)
  rw [TateModule.coe_zero, Pi.zero_apply]
  refine hnd k _ (TateModule.torsion x k) fun v hv => ?_
  obtain ⟨y, hy⟩ := exists_tateModule_apply_eq hdiv k v hv
  have h := congrArg (PadicInt.toZModPow k) (hx y)
  rw [toZModPow_pair, map_zero, hy] at h
  exact eq_one_of_dlog_eq_zero p (E.pow_eq_one k _ _ (TateModule.torsion x k) hv) h

theorem pair_self (halt : ∀ (k : ℕ) (u : J), ((p ^ k : ℕ) : ℤ) • u = 0 → E.e k u u = 1)
    (x : TateModule p J) : E.pair x x = 0 := by
  refine PadicInt.ext_of_toZModPow.1 fun k => ?_
  rw [toZModPow_pair, map_zero, halt k _ (TateModule.torsion x k)]
  exact (dlog_eq_natCast p (k := k) (c := 0) (pow_zero _)).trans Nat.cast_zero

noncomputable def form : LinearMap.BilinForm ℚ_[p] (ℚ_[p] ⊗[ℤ_[p]] TateModule p J) :=
  LinearMap.BilinForm.baseChange ℚ_[p] E.pairing

theorem form_tmul (a a' : ℚ_[p]) (x y : TateModule p J) :
    E.form (a ⊗ₜ x) (a' ⊗ₜ y) = E.pair x y • (a * a') :=
  LinearMap.BilinForm.baseChange_tmul _ _ _ _ _

theorem form_baseChange_adjoint (F F' : Module.End ℤ_[p] (TateModule p J))
    (h : ∀ x y, E.pair (F x) y = E.pair x (F' y)) (z w : ℚ_[p] ⊗[ℤ_[p]] TateModule p J) :
    E.form (F.baseChange ℚ_[p] z) w = E.form z (F'.baseChange ℚ_[p] w) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a' y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, form_tmul, form_tmul, h]
    | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw']
  | add z z' hz hz' =>
    rw [map_add, map_add, LinearMap.add_apply, hz, hz', map_add, LinearMap.add_apply]

theorem form_baseChange_scale (G : Module.End ℤ_[p] (TateModule p J)) (q : ℕ)
    (h : ∀ x y, E.pair (G x) (G y) = (q : ℤ_[p]) * E.pair x y)
    (z w : ℚ_[p] ⊗[ℤ_[p]] TateModule p J) :
    E.form (G.baseChange ℚ_[p] z) (G.baseChange ℚ_[p] w) = (q : ℚ_[p]) • E.form z w := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a' y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, form_tmul, form_tmul, h,
        mul_smul, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', smul_add]
  | add z z' hz hz' =>
    rw [map_add, map_add, LinearMap.add_apply, hz, hz', map_add, LinearMap.add_apply, smul_add]

theorem exists_smul_eq_one_tmul (z : ℚ_[p] ⊗[ℤ_[p]] TateModule p J) :
    ∃ (s : nonZeroDivisors ℤ_[p]) (t : TateModule p J),
      (s : ℤ_[p]) • z = (1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] t := by
  obtain ⟨⟨t, s⟩, h⟩ :=
    IsLocalizedModule.surj (nonZeroDivisors ℤ_[p]) (TensorProduct.mk ℤ_[p] ℚ_[p] (TateModule p J) 1) z
  exact ⟨s, t, h⟩

theorem form_one_tmul (t y : TateModule p J) :
    E.form ((1 : ℚ_[p]) ⊗ₜ t) ((1 : ℚ_[p]) ⊗ₜ y) = algebraMap ℤ_[p] ℚ_[p] (E.pair t y) := by
  rw [form_tmul, mul_one, Algebra.algebraMap_eq_smul_one]

theorem eq_zero_of_nonZeroDivisors_smul {s : nonZeroDivisors ℤ_[p]}
    {z : ℚ_[p] ⊗[ℤ_[p]] TateModule p J} (h : (s : ℤ_[p]) • z = 0) : z = 0 := by
  rw [← algebraMap_smul ℚ_[p] (s : ℤ_[p]) z] at h
  have hne : algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  rw [← one_smul ℚ_[p] z, ← inv_mul_cancel₀ hne, mul_smul, h, smul_zero]

theorem form_nondeg_left (hT : ∀ x : TateModule p J, (∀ y, E.pair x y = 0) → x = 0)
    (z : ℚ_[p] ⊗[ℤ_[p]] TateModule p J) (hz : ∀ w, E.form z w = 0) : z = 0 := by
  obtain ⟨s, t, hst⟩ := exists_smul_eq_one_tmul z
  have ht : t = 0 := hT t fun y => by
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    rw [map_zero, ← form_one_tmul, ← hst, ← algebraMap_smul ℚ_[p] (s : ℤ_[p]) z, map_smul,
      LinearMap.smul_apply, hz, smul_zero]
  rw [ht, tmul_zero] at hst
  exact eq_zero_of_nonZeroDivisors_smul hst

theorem form_self (hT : ∀ x : TateModule p J, E.pair x x = 0)
    (z : ℚ_[p] ⊗[ℤ_[p]] TateModule p J) : E.form z z = 0 := by
  obtain ⟨s, t, hst⟩ := exists_smul_eq_one_tmul z
  have hne : algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have h : algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) * (algebraMap ℤ_[p] ℚ_[p] (s : ℤ_[p]) * E.form z z)
      = 0 := by
    rw [← smul_eq_mul, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul, ← map_smul,
      algebraMap_smul, hst, form_one_tmul, hT, map_zero]
  simpa [hne] using h

end LevelPairing
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing"

theorem assembleH {K : Type*} [Field K] [IsAlgClosed K] [CharZero K] {p : ℕ} [hp : Fact p.Prime]
    {J : Type} [AddCommGroup J]
    {Γ : Type} [Group Γ] [DistribMulAction Γ J] (χ : Γ → K → K)
    (e : ℕ → J → J → K)
    (he1 : ∀ (n : ℕ) (x y : J), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1)
    (he2 : ∀ (n : ℕ) (x x' y : J), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
      e n (x + x') y = e n x y * e n x' y)
    (he3 : ∀ (n : ℕ) (x y y' : J), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
      e n x (y + y') = e n x y * e n x y')
    (he4 : ∀ (n : ℕ) (x : J), 0 < n → (n : ℤ) • x = 0 →
      (∀ y : J, (n : ℤ) • y = 0 → e n x y = 1) → x = 0)
    (he6 : ∀ (n m : ℕ) (x y : J), 0 < n → 0 < m →
      ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
      e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m)
    (he7 : ∀ (n : ℕ) (g : Γ) (x y : J), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n (g • x) (g • y) = χ g (e n x y))
    (he9 : ∀ (n : ℕ) (x y : J), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n x y * e n y x = 1)
    (W : Γ) (hW2 : ∀ u : J, W • W • u = u) (hχW : ∀ z : K, χ W z = z)
    (hdiv : ∀ u : J, ∃ v : J, ((p : ℕ) : ℤ) • v = u) :
    ∃ B : (ℚ_[p] ⊗[ℤ_[p]] TateModule p J) →ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p J) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ f : J →+ J,
        (∀ (n : ℕ) (u v : J), 0 < n → (n : ℤ) • u = 0 → (n : ℤ) • v = 0 →
          e n (f u) (W • v) = e n u (W • f v)) →
        ∀ x y, B ((TateModule.rep p J (AddMonoid.End J) f).baseChange ℚ_[p] x) y
          = B x ((TateModule.rep p J (AddMonoid.End J) f).baseChange ℚ_[p] y)) ∧
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      (∀ (g d : Γ) (ℓ : ℕ), (∀ (k : ℕ) (ζ : K), ζ ^ p ^ k = 1 → χ g ζ = ζ ^ ℓ) →
        (∀ z : K, χ d z = z) → (∀ u : J, d • g • u = g • d • u) → (∀ u : J, W • g • u = g • d • W • u) →
        ∀ x y,
          B ((TateModule.rep p J Γ d).baseChange ℚ_[p] ((TateModule.rep p J Γ g).baseChange ℚ_[p] x))
              ((TateModule.rep p J Γ g).baseChange ℚ_[p] y)
            = (ℓ : ℚ_[p]) * B x y) ∧
      ∀ (g d : Γ) (u : ℤ_[p]),
        (∀ (k : ℕ) (ζ : K), ζ ^ p ^ k = 1 → χ g ζ = ζ ^ (PadicInt.toZModPow k u).val) →
        (∀ z : K, χ d z = z) → (∀ u : J, d • g • u = g • d • u) → (∀ u : J, W • g • u = g • d • W • u) →
        ∀ x y,
          B ((TateModule.rep p J Γ d).baseChange ℚ_[p] ((TateModule.rep p J Γ g).baseChange ℚ_[p] x))
              ((TateModule.rep p J Γ g).baseChange ℚ_[p] y)
            = (u : ℚ_[p]) * B x y := by
  have hpk : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp.out.pos k
  have hΓz : ∀ (g : Γ) (m : ℤ) (v : J), g • (m • v) = m • (g • v) := fun g m v =>
    map_zsmul (DistribSMul.toAddMonoidHom J g) m v
  have hΓt : ∀ (g : Γ) {m : ℤ} {v : J}, m • v = 0 → m • (g • v) = 0 := fun g {m v} hv => by
    rw [← hΓz, hv, smul_zero]

  have hEex : ∃ E : LevelPairing K p J, ∀ k u v, E.e k u v = e (p ^ k) u (W • v) := by
    refine ⟨{ e := fun k u v => e (p ^ k) u (W • v)
              pow_eq_one := fun k u v hu hv => he1 _ _ _ (hpk k) hu (hΓt W hv)
              add_left := fun k u u' v hu hu' hv => he2 _ _ _ _ (hpk k) hu hu' (hΓt W hv)
              add_right := fun k u v v' hu hv hv' => ?_
              compat := fun k u v hu hv => ?_ }, fun _ _ _ => rfl⟩
    · show e (p ^ k) u (W • (v + v')) = _
      rw [smul_add]; exact he3 _ _ _ _ (hpk k) hu (hΓt W hv) (hΓt W hv')
    · show e (p ^ k) _ (W • _) = e (p ^ (k + 1)) u (W • v) ^ p
      rw [hΓz, pow_succ p k]
      rw [pow_succ p k] at hu hv
      exact he6 (p ^ k) p u (W • v) (hpk k) hp.out.pos hu (hΓt W hv)
  obtain ⟨E, hE⟩ := hEex

  have hndL : ∀ (k : ℕ) (u : J), ((p ^ k : ℕ) : ℤ) • u = 0 →
      (∀ v, ((p ^ k : ℕ) : ℤ) • v = 0 → E.e k u v = 1) → u = 0 := fun k u hu h =>
    he4 _ u (hpk k) hu fun y hy => by
      have := h (W⁻¹ • y) (hΓt W⁻¹ hy)
      rwa [hE, smul_inv_smul] at this

  have hsq : ∀ (k : ℕ) (u : J), ((p ^ k : ℕ) : ℤ) • u = 0 → E.e k u u * E.e k u u = 1 := by
    intro k u hu
    have hWu : W • (W • u) = u := hW2 u
    have h7 := he7 (p ^ k) W u (W • u) (hpk k) hu (hΓt W hu)
    rw [hWu, hχW] at h7
    calc E.e k u u * E.e k u u
        = e (p ^ k) u (W • u) * e (p ^ k) (W • u) u := by rw [hE, h7]
      _ = 1 := he9 (p ^ k) u (W • u) (hpk k) hu (hΓt W hu)
  have halt : ∀ (k : ℕ) (u : J), ((p ^ k : ℕ) : ℤ) • u = 0 → E.e k u u = 1 := by
    intro k u hu
    rcases hp.out.eq_two_or_odd' with h2 | hodd
    · obtain ⟨u', rfl⟩ := hdiv u
      have hu' : ((p ^ (k + 1) : ℕ) : ℤ) • u' = 0 := by
        rw [pow_succ, Nat.cast_mul, mul_smul]; exact hu
      rw [E.compat k u' u' hu' hu']
      have hp2 : E.e (k + 1) u' u' ^ p = (E.e (k + 1) u' u' * E.e (k + 1) u' u') ^ (p / 2) := by
        rw [← sq, ← pow_mul]; congr 1; omega
      rw [hp2, hsq (k + 1) u' hu', one_pow]
    · obtain ⟨m, hm⟩ : Odd (p ^ k) := hodd.pow
      have h1 := E.pow_eq_one k u u hu hu
      rw [hm, pow_succ, pow_mul, sq, hsq k u hu, one_pow, one_mul] at h1
      exact h1
  refine ⟨E.form, ?_, E.form_self (E.pair_self halt),
    fun x hx => E.form_nondeg_left (E.pair_nondeg_left hdiv hndL) x hx, ?_, ?_⟩
  ·
    intro f hf x y
    have hft : ∀ {m : ℤ} {u : J}, m • u = 0 → m • (f u) = 0 := fun {m u} hu => by
      rw [← map_zsmul, hu, map_zero]
    exact E.form_baseChange_adjoint _ _ (fun x y => E.pair_eq_of_forall fun k => by
      rw [TateModule.rep_apply, TateModule.rep_apply, hE, hE]
      exact hf (p ^ k) _ _ (hpk k) (TateModule.torsion x k) (TateModule.torsion y k)) x y
  ·
    intro g d ℓ hχg hχd hdg hWg x y

    have HG : ∀ (k : ℕ) (u v : J), ((p ^ k : ℕ) : ℤ) • u = 0 → ((p ^ k : ℕ) : ℤ) • v = 0 →
        E.e k (d • (g • u)) (g • v) = E.e k u v ^ ℓ := by
      intro k u v hu hv
      rw [hE, hE, hdg, hWg, he7 (p ^ k) g _ _ (hpk k) (hΓt d hu) (hΓt d (hΓt W hv)),
        he7 (p ^ k) d _ _ (hpk k) hu (hΓt W hv), hχd]
      exact hχg k _ (he1 _ _ _ (hpk k) hu (hΓt W hv))

    have HT : ∀ x y : TateModule p J,
        E.pair (TateModule.rep p J Γ d (TateModule.rep p J Γ g x)) (TateModule.rep p J Γ g y)
          = (ℓ : ℤ_[p]) * E.pair x y := fun x y =>
      E.pair_eq_natCast_mul fun k => by
        rw [TateModule.rep_apply, TateModule.rep_apply, TateModule.rep_apply]
        exact HG k _ _ (TateModule.torsion x k) (TateModule.torsion y k)

    have key : ∀ (z w : ℚ_[p] ⊗[ℤ_[p]] TateModule p J),
        E.form ((TateModule.rep p J Γ d * TateModule.rep p J Γ g).baseChange ℚ_[p] z)
            ((TateModule.rep p J Γ g).baseChange ℚ_[p] w) = (ℓ : ℚ_[p]) • E.form z w := by
      intro z w
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul a' y =>
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LevelPairing.form_tmul,
            LevelPairing.form_tmul, Module.End.mul_apply, HT, mul_smul, Nat.cast_smul_eq_nsmul,
            Nat.cast_smul_eq_nsmul]
        | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', smul_add]
      | add z z' hz hz' =>
        rw [map_add, map_add, LinearMap.add_apply, hz, hz', map_add, LinearMap.add_apply, smul_add]
    have hcomp : (TateModule.rep p J Γ d).baseChange ℚ_[p] ((TateModule.rep p J Γ g).baseChange ℚ_[p] x)
        = (TateModule.rep p J Γ d * TateModule.rep p J Γ g).baseChange ℚ_[p] x := by
      rw [Module.End.mul_eq_comp, LinearMap.baseChange_comp]; rfl
    rw [hcomp, key, smul_eq_mul]
  ·
    intro g d u hχg hχd hdg hWg x y
    have HG : ∀ (k : ℕ) (a v : J), ((p ^ k : ℕ) : ℤ) • a = 0 → ((p ^ k : ℕ) : ℤ) • v = 0 →
        E.e k (d • (g • a)) (g • v) = E.e k a v ^ (PadicInt.toZModPow k u).val := by
      intro k a v ha hv
      rw [hE, hE, hdg, hWg, he7 (p ^ k) g _ _ (hpk k) (hΓt d ha) (hΓt d (hΓt W hv)),
        he7 (p ^ k) d _ _ (hpk k) ha (hΓt W hv), hχd]
      exact hχg k _ (he1 _ _ _ (hpk k) ha (hΓt W hv))
    have HT : ∀ x y : TateModule p J,
        E.pair (TateModule.rep p J Γ d (TateModule.rep p J Γ g x)) (TateModule.rep p J Γ g y)
          = u * E.pair x y := fun x y =>
      E.pair_eq_mul_of_toZModPow fun k => by
        rw [TateModule.rep_apply, TateModule.rep_apply, TateModule.rep_apply]
        exact HG k _ _ (TateModule.torsion x k) (TateModule.torsion y k)
    have key : ∀ (z w : ℚ_[p] ⊗[ℤ_[p]] TateModule p J),
        E.form ((TateModule.rep p J Γ d * TateModule.rep p J Γ g).baseChange ℚ_[p] z)
            ((TateModule.rep p J Γ g).baseChange ℚ_[p] w) = (u : ℚ_[p]) • E.form z w := by
      intro z w
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul a' y =>
          rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, LevelPairing.form_tmul,
            LevelPairing.form_tmul, Module.End.mul_apply, HT, mul_smul, ← algebraMap_smul ℚ_[p] u,
            smul_eq_mul]
          rfl
        | add w w' hw hw' => rw [map_add, map_add, map_add, hw, hw', smul_add]
      | add z z' hz hz' =>
        rw [map_add, map_add, LinearMap.add_apply, hz, hz', map_add, LinearMap.add_apply, smul_add]
    have hcomp : (TateModule.rep p J Γ d).baseChange ℚ_[p] ((TateModule.rep p J Γ g).baseChange ℚ_[p] x)
        = (TateModule.rep p J Γ d * TateModule.rep p J Γ g).baseChange ℚ_[p] x := by
      rw [Module.End.mul_eq_comp, LinearMap.baseChange_comp]; rfl
    rw [hcomp, key, smul_eq_mul]

end SimilitudeEngineH
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH"

set_option maxHeartbeats 1600000

namespace KSimJH

open AlgebraicCurve ModularCurve CongruenceSubgroup
open scoped MatrixGroups

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

local notation "𝕂" => AlgebraicClosure ℚ

scoped instance finiteIndex_GammaH : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance finiteIndex_inf (ℓ : ℕ) [NeZero ℓ] : (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (Gamma1_le_GammaH M H)

omit [NeZero M] in
theorem T_mem_inf (ℓ : ℕ) : ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem presentation_bot :
    ∃ x : xHFunctionFieldBar M H, Transcendental 𝕂 x ∧
      FiniteDimensional (IntermediateField.adjoin 𝕂 ({x} : Set (xHFunctionFieldBar M H)))
        (xHFunctionFieldBar M H) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange 𝕂
    (CohCarrier.GammaH M H) (translation_mem_GammaH M H)

theorem presentation_top (ℓ : ℕ) [NeZero ℓ] :
    ∃ x : laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ)), Transcendental 𝕂 x ∧
      FiniteDimensional (IntermediateField.adjoin 𝕂
        ({x} : Set (laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ)))))
        (laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
  ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange 𝕂
    (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) (T_mem_inf M H ℓ)

omit [NeZero M] in
theorem transcendental_map {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] (φ : F →ₐ[K] F') {x : F} (hx : Transcendental K x) : Transcendental K (φ x) := by
  rintro ⟨q, hq0, hq⟩
  refine hx ⟨q, hq0, ?_⟩
  rw [Polynomial.aeval_algHom_apply] at hq
  exact (map_eq_zero_iff φ (RingHom.injective (φ : F →+* F'))).mp hq

omit [NeZero M] in

theorem finiteAlong_of_finiteDimensional_adjoin {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (x : F)
    [h : FiniteDimensional (IntermediateField.adjoin K ({φ x} : Set F')) F'] : FiniteAlong K φ := by
  letI := algebraAlong φ
  show Module.Finite F F'
  set E := IntermediateField.adjoin K ({φ x} : Set F')
  have hE : E ≤ φ.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := Module.finite_def.mp h
  refine Module.finite_def.mpr ⟨s, ?_⟩
  rw [eq_top_iff]
  rintro y -
  have hy : y ∈ Submodule.span E (s : Set F') := by rw [hs]; trivial
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      obtain ⟨b, hb⟩ := AlgHom.mem_fieldRange.mp (hE c.2)
      have : (c • a : F') = b • a := by
        show (c : F') * a = φ.toRingHom b * a
        rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hb]
      rw [this]
      exact Submodule.smul_mem _ b ha

theorem finiteAlong_of_hom (ℓ : ℕ) [NeZero ℓ]
    (φ : xHFunctionFieldBar M H →ₐ[𝕂] laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ))) :
    FiniteAlong 𝕂 φ := by
  obtain ⟨xT, -, hfdT⟩ := presentation_top M H ℓ
  obtain ⟨xB, hxB, -⟩ := presentation_bot M H
  haveI := hfdT
  have htr : Transcendental 𝕂 (φ xB) := transcendental_map φ hxB
  haveI := AlgebraicCurve.finiteDimensional_adjoin_of_transcendental xT htr
  exact finiteAlong_of_finiteDimensional_adjoin φ xB

omit [NeZero M] in
theorem charZero_bot : CharZero (xHFunctionFieldBar M H) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (xHFunctionFieldBar M H)).injective

section Levelwise

variable (e : ℕ → JH M H → JH M H → 𝕂) (W : SemilinearAut 𝕂 (xHFunctionFieldBar M H))

theorem adjoint_T (hin : HeckeDiamondInputsHAll M H)
    (he8 : ∀ (F' : Type) [Field F'] [Algebra 𝕂 F'] [HasPrincipalDivisors 𝕂 F']
      (φ ψ : xHFunctionFieldBar M H →ₐ[𝕂] F') (hφ : φ.toRingHom.IsIntegral)
      (hψ : ψ.toRingHom.IsIntegral)
      (hFIφ : FundamentalIdentityAlong 𝕂 φ hφ) (hfinψ : FiniteAlong 𝕂 ψ)
      (hNψ : NormFormulaAlong 𝕂 ψ hfinψ)
      (hFIψ : FundamentalIdentityAlong 𝕂 ψ hψ) (hfinφ : FiniteAlong 𝕂 φ)
      (hNφ : NormFormulaAlong 𝕂 φ hfinφ)
      (n : ℕ) (x y : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n (Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x) y
        = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y))
    (hw1 : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (hα : HeckeAlphaHBarIntegral 𝕂 M H ℓ) (hβ : HeckeBetaHBarIntegral 𝕂 M H ℓ)
      [HasPrincipalDivisors 𝕂 (laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
      (hFIβ : FundamentalIdentityAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ) hβ)
      (hfinα : FiniteAlong 𝕂 (heckeAlphaHBar 𝕂 M H ℓ))
      (hNα : NormFormulaAlong 𝕂 (heckeAlphaHBar 𝕂 M H ℓ) hfinα)
      (hFIα : FundamentalIdentityAlong 𝕂 (heckeAlphaHBar 𝕂 M H ℓ) hα)
      (hfinβ : FiniteAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ))
      (hNβ : NormFormulaAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ) hfinβ)
      (x : JH M H),
      heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (W • x) = W • heckePic0HBar hα hβ hFIβ hfinα hNα x)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (n : ℕ) (u v : JH M H) (hn : 0 < n) (hu : (n : ℤ) • u = 0)
    (hWv : (n : ℤ) • (W • v) = 0) :
    e n ((haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong 𝕂 M H ℓ) u) (W • v)
      = e n u (W • (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong 𝕂 M H ℓ) v) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨h0, hα, hβ, hPD, hfinα, hFIβ, hNα⟩ := hin.1 ℓ hℓ
  haveI := hPD
  haveI := charZero_bot M H
  have hfinβ : FiniteAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ) := finiteAlong_of_hom M H ℓ _
  have hFIα := AlgebraicCurve.fundamentalIdentityAlong _ hα hfinα
    (AlgebraicCurve.separableAlong_of_charZero _ hα)
  have hNβ := AlgebraicCurve.normFormulaAlong _ hfinβ (AlgebraicCurve.separableAlong_of_charZero _ hβ)
  have hT : (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHAlong 𝕂 M H ℓ)
      = heckePic0HBar hα hβ hFIβ hfinα hNα :=
    heckeOperatorHAlong_eq h0 hα hβ hFIβ hfinα hNα
  have h8 := he8 (laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ)))
    (heckeBetaHBar 𝕂 M H ℓ) (heckeAlphaHBar 𝕂 M H ℓ) hβ hα hFIβ hfinα hNα hFIα hfinβ hNβ n u (W • v)
    hn hu hWv
  have h2b := hw1 ℓ hα hβ hFIβ hfinα hNα hFIα hfinβ hNβ v
  rw [hT]
  exact h8.trans (congrArg (e n u) h2b)

omit [NeZero M] in

theorem adjoint_dia
    (he7 : ∀ (n : ℕ) (g : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (x y : JH M H), 0 < n →
      (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n (g • x) (g • y) = SemilinearAut.baseAut g (e n x y))
    (hw2 : ∀ (d : (ZMod M)ˣ) (x : JH M H), diamondHBar M H d (W • diamondHBar M H d x) = W • x)
    (d : (ZMod M)ˣ) (n : ℕ) (u v : JH M H) (hn : 0 < n) (hu : (n : ℤ) • u = 0)
    (hWv : (n : ℤ) • (W • v) = 0) :
    e n (diamondHBar M H d u) (W • v) = e n u (W • diamondHBar M H d v) := by
  obtain ⟨D, hDu, hχD⟩ : ∃ D : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ z : JH M H, diamondHBar M H d z = D • z) ∧ ∀ z : 𝕂, SemilinearAut.baseAut D z = z :=
    ⟨_, diamondHBar_apply M H d, fun _ => rfl⟩
  have hDt : ∀ (g : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) {m : ℤ} {z : JH M H},
      m • z = 0 → m • (g • z) = 0 := fun g {m z} hz => by
    rw [← SemilinearAut.smul_zsmul, hz]; exact smul_zero (A := JH M H) g
  have key : D⁻¹ • (W • v) = W • (D • v) := by
    have h2 : D • (W • (D • v)) = W • v := by rw [← hDu, ← hDu]; exact hw2 d v
    rw [← h2, inv_smul_smul]
  rw [hDu, hDu]
  calc e n (D • u) (W • v) = e n (D • u) (D • (D⁻¹ • (W • v))) := by rw [smul_inv_smul]
    _ = SemilinearAut.baseAut D (e n u (D⁻¹ • (W • v))) := he7 n D u _ hn hu (hDt D⁻¹ hWv)
    _ = e n u (D⁻¹ • (W • v)) := hχD _
    _ = e n u (W • (D • v)) := by rw [key]

omit [NeZero M] in

theorem galois_data (p : ℕ) [Fact p.Prime] (σ : 𝕂 ≃ₐ[ℚ] 𝕂) :
    ∃ g : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ z : JH M H, σ • z = g • z) ∧ (∀ z : 𝕂, SemilinearAut.baseAut g z = σ z) ∧
      TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g
        = JH.tateGaloisRep M H p σ := by
  obtain ⟨g, hgu, hgz⟩ : ∃ g : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ z : JH M H, σ • z = g • z) ∧ ∀ z : 𝕂, SemilinearAut.baseAut g z = σ z :=
    ⟨_, galois_smul_pic0_def (xHFunctionField M H) σ, fun _ => rfl⟩
  exact ⟨g, hgu, hgz,
    LinearMap.ext fun z => Subtype.ext (funext fun n => (hgu ((z : ℕ → JH M H) n)).symm)⟩

omit [NeZero M] in

theorem dia_data (p : ℕ) [Fact p.Prime] (u₀ : (ZMod M)ˣ) :
    ∃ D : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ z : JH M H, diamondHBar M H u₀ z = D • z) ∧ (∀ z : 𝕂, SemilinearAut.baseAut D z = z) ∧
      TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) D
        = JH.tateEnd M H p (diamondHBar M H u₀) := by
  obtain ⟨D, hDu, hχD⟩ : ∃ D : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ z : JH M H, diamondHBar M H u₀ z = D • z) ∧ ∀ z : 𝕂, SemilinearAut.baseAut D z = z :=
    ⟨_, diamondHBar_apply M H u₀, fun _ => rfl⟩
  exact ⟨D, hDu, hχD,
    LinearMap.ext fun z => Subtype.ext (funext fun n => (hDu ((z : ℕ → JH M H) n)).symm)⟩

theorem twist_data (p : ℕ) [Fact p.Prime] (u₀ : (ZMod M)ˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring 𝕂) (hA : A.LiesOverPrime ℓ) (σ : 𝕂 ≃ₐ[ℚ] 𝕂) (hσ : A.IsFrobeniusAt σ ℓ)
    (hw4 : ∀ x : JH M H, W • (σ • x) = σ • diamondHBar M H u₀ (W • x)) :
    ∃ g D : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ (k : ℕ) (ζ : 𝕂), ζ ^ p ^ k = 1 → SemilinearAut.baseAut g ζ = ζ ^ ℓ) ∧
      (∀ z : 𝕂, SemilinearAut.baseAut D z = z) ∧
      (∀ P : JH M H, D • g • P = g • D • P) ∧
      (∀ P : JH M H, W • g • P = g • D • W • P) ∧
      TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g
        = JH.tateGaloisRep M H p σ ∧
      TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) D
        = JH.tateEnd M H p (diamondHBar M H u₀) := by
  have hp : Fact p.Prime := inferInstance
  obtain ⟨g, hgu, hgz, e1⟩ := galois_data M H p σ
  obtain ⟨D, hDu, hχD, e2⟩ := dia_data M H p u₀
  refine ⟨g, D, ?_, hχD, ?_, ?_, e1, e2⟩
  · intro k ζ hζ
    have hne : p ≠ ℓ := fun h => hℓp h.symm
    have hcop : (p ^ k).Coprime ℓ := ((Nat.coprime_primes hp.out hℓ).mpr hne).pow_left k
    rw [hgz]
    exact ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ ℓ (p ^ k) hA hσ hcop ζ hζ
  · intro P
    have hc : σ • diamondHBar M H u₀ P = diamondHBar M H u₀ (σ • P) :=
      galois_smul_genOpH_comm M H (∅ : Set ℕ) σ (CohCarrier.Gen.dia u₀) P
    calc D • g • P = diamondHBar M H u₀ (g • P) := (hDu _).symm
      _ = diamondHBar M H u₀ (σ • P) := congrArg (diamondHBar M H u₀) (hgu P).symm
      _ = σ • diamondHBar M H u₀ P := hc.symm
      _ = g • diamondHBar M H u₀ P := hgu _
      _ = g • D • P := congrArg (g • ·) (hDu P)
  · intro P
    calc W • g • P = W • σ • P := congrArg (W • ·) (hgu P).symm
      _ = σ • diamondHBar M H u₀ (W • P) := hw4 P
      _ = g • diamondHBar M H u₀ (W • P) := hgu _
      _ = g • D • W • P := congrArg (g • ·) (hDu _)

end Levelwise
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH"

section Simil

variable (W : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (p : ℕ) [Fact p.Prime]

theorem simil
    (B : (ℚ_[p] ⊗[ℤ_[p]] TateModule p (JH M H)) →ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (JH M H))
      →ₗ[ℚ_[p]] ℚ_[p])
    (hsim : ∀ (g d : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (ℓ : ℕ),
      (∀ (k : ℕ) (ζ : 𝕂), ζ ^ p ^ k = 1 → SemilinearAut.baseAut g ζ = ζ ^ ℓ) →
      (∀ z : 𝕂, SemilinearAut.baseAut d z = z) → (∀ u : JH M H, d • g • u = g • d • u) →
      (∀ u : JH M H, W • g • u = g • d • W • u) →
      ∀ x y,
        B ((TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) d).baseChange ℚ_[p]
            ((TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g).baseChange
              ℚ_[p] x))
          ((TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g).baseChange ℚ_[p] y)
          = (ℓ : ℚ_[p]) * B x y)
    (u₀ : (ZMod M)ˣ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (A : ValuationSubring 𝕂) (hA : A.LiesOverPrime ℓ) (σ : 𝕂 ≃ₐ[ℚ] 𝕂) (hσ : A.IsFrobeniusAt σ ℓ)
    (hw4 : ∀ x : JH M H, W • (σ • x) = σ • diamondHBar M H u₀ (W • x))
    (x y : ℚ_[p] ⊗[ℤ_[p]] TateModule p (JH M H)) :
    B ((JH.tateEnd M H p (diamondHBar M H u₀)).baseChange ℚ_[p]
        ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x)) ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y)
      = (ℓ : ℚ_[p]) * B x y := by
  obtain ⟨g, D, hχg, hχD, hdg, hWg, e1, e2⟩ := twist_data M H W p u₀ hℓ hℓp A hA σ hσ hw4
  have key : ∀ Fg FD : Module.End ℤ_[p] (TateModule p (JH M H)),
      Fg = TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g →
      FD = TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) D →
      B (FD.baseChange ℚ_[p] (Fg.baseChange ℚ_[p] x)) (Fg.baseChange ℚ_[p] y) = (ℓ : ℚ_[p]) * B x y := by
    rintro _ _ rfl rfl
    exact hsim g D ℓ hχg hχD hdg hWg x y
  exact key _ _ e1.symm e2.symm

end Simil
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH"

section Cyclo

variable (W : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (p : ℕ) [Fact p.Prime]

theorem cyclo_data (σ : 𝕂 ≃ₐ[ℚ] 𝕂) (c : ℕ) (hc : c.Coprime M)
    (hw5 : ∀ x : JH M H, W • (σ • x) = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (W • x)) :
    ∃ g D : SemilinearAut 𝕂 (xHFunctionFieldBar M H),
      (∀ (k : ℕ) (ζ : 𝕂), ζ ^ p ^ k = 1 → SemilinearAut.baseAut g ζ =
        ζ ^ (PadicInt.toZModPow k
          ((cyclotomicCharacter 𝕂 p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])).val) ∧
      (∀ z : 𝕂, SemilinearAut.baseAut D z = z) ∧
      (∀ P : JH M H, D • g • P = g • D • P) ∧
      (∀ P : JH M H, W • g • P = g • D • W • P) ∧
      TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g
        = JH.tateGaloisRep M H p σ ∧
      TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) D
        = JH.tateEnd M H p (diamondHBar M H (ZMod.unitOfCoprime c hc)) := by
  obtain ⟨g, hgu, hgz, e1⟩ := galois_data M H p σ
  obtain ⟨D, hDu, hχD, e2⟩ := dia_data M H p (ZMod.unitOfCoprime c hc)
  refine ⟨g, D, ?_, hχD, ?_, ?_, e1, e2⟩
  · intro k ζ hζ
    rw [hgz]
    exact cyclotomicCharacter.spec p σ.toRingEquiv ζ hζ
  · intro P
    have hcm : σ • diamondHBar M H (ZMod.unitOfCoprime c hc) P =
        diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • P) :=
      galois_smul_genOpH_comm M H (∅ : Set ℕ) σ (CohCarrier.Gen.dia (ZMod.unitOfCoprime c hc)) P
    calc D • g • P = diamondHBar M H (ZMod.unitOfCoprime c hc) (g • P) := (hDu _).symm
      _ = diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • P) := congrArg (diamondHBar M H _) (hgu P).symm
      _ = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) P := hcm.symm
      _ = g • diamondHBar M H (ZMod.unitOfCoprime c hc) P := hgu _
      _ = g • D • P := congrArg (g • ·) (hDu P)
  · intro P
    calc W • g • P = W • σ • P := congrArg (W • ·) (hgu P).symm
      _ = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (W • P) := hw5 P
      _ = g • diamondHBar M H (ZMod.unitOfCoprime c hc) (W • P) := hgu _
      _ = g • D • W • P := congrArg (g • ·) (hDu _)

theorem simil_cyc
    (B : (ℚ_[p] ⊗[ℤ_[p]] TateModule p (JH M H)) →ₗ[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (JH M H))
      →ₗ[ℚ_[p]] ℚ_[p])
    (hsimu : ∀ (g d : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (u : ℤ_[p]),
      (∀ (k : ℕ) (ζ : 𝕂), ζ ^ p ^ k = 1 → SemilinearAut.baseAut g ζ = ζ ^ (PadicInt.toZModPow k u).val) →
      (∀ z : 𝕂, SemilinearAut.baseAut d z = z) → (∀ u : JH M H, d • g • u = g • d • u) →
      (∀ u : JH M H, W • g • u = g • d • W • u) →
      ∀ x y,
        B ((TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) d).baseChange ℚ_[p]
            ((TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g).baseChange
              ℚ_[p] x))
          ((TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g).baseChange ℚ_[p] y)
          = (u : ℚ_[p]) * B x y)
    (σ : 𝕂 ≃ₐ[ℚ] 𝕂) (c : ℕ) (hc : c.Coprime M)
    (hw5 : ∀ x : JH M H, W • (σ • x) = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (W • x))
    (x y : ℚ_[p] ⊗[ℤ_[p]] TateModule p (JH M H)) :
    B ((JH.tateEnd M H p (diamondHBar M H (ZMod.unitOfCoprime c hc))).baseChange ℚ_[p]
        ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x)) ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y)
      = (((cyclotomicCharacter 𝕂 p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * B x y := by
  obtain ⟨g, D, hχg, hχD, hdg, hWg, e1, e2⟩ := cyclo_data M H W p σ c hc hw5
  have key : ∀ Fg FD : Module.End ℤ_[p] (TateModule p (JH M H)),
      Fg = TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) g →
      FD = TateModule.rep p (JH M H) (SemilinearAut 𝕂 (xHFunctionFieldBar M H)) D →
      B (FD.baseChange ℚ_[p] (Fg.baseChange ℚ_[p] x)) (Fg.baseChange ℚ_[p] y) =
        (((cyclotomicCharacter 𝕂 p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * B x y := by
    rintro _ _ rfl rfl
    exact hsimu g D _ hχg hχD hdg hWg x y
  exact key _ _ e1.symm e2.symm

end Cyclo
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH"

theorem core (p : ℕ) [Fact p.Prime] (hin : HeckeDiamondInputsHAll M H)
    (e : ℕ → JH M H → JH M H → 𝕂)
    (he1 : ∀ (n : ℕ) (x y : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → e n x y ^ n = 1)
    (he2 : ∀ (n : ℕ) (x x' y : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • x' = 0 → (n : ℤ) • y = 0 →
      e n (x + x') y = e n x y * e n x' y)
    (he3 : ∀ (n : ℕ) (x y y' : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 → (n : ℤ) • y' = 0 →
      e n x (y + y') = e n x y * e n x y')
    (he4 : ∀ (n : ℕ) (x : JH M H), 0 < n → (n : ℤ) • x = 0 →
      (∀ y : JH M H, (n : ℤ) • y = 0 → e n x y = 1) → x = 0)
    (he6 : ∀ (n m : ℕ) (x y : JH M H), 0 < n → 0 < m →
      ((n * m : ℕ) : ℤ) • x = 0 → ((n * m : ℕ) : ℤ) • y = 0 →
      e n ((m : ℤ) • x) ((m : ℤ) • y) = e (n * m) x y ^ m)
    (he7 : ∀ (n : ℕ) (g : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (x y : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n (g • x) (g • y) = SemilinearAut.baseAut g (e n x y))
    (he8 : ∀ (F' : Type) [Field F'] [Algebra 𝕂 F'] [HasPrincipalDivisors 𝕂 F']
      (φ ψ : xHFunctionFieldBar M H →ₐ[𝕂] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
      (hFIφ : FundamentalIdentityAlong 𝕂 φ hφ) (hfinψ : FiniteAlong 𝕂 ψ)
      (hNψ : NormFormulaAlong 𝕂 ψ hfinψ)
      (hFIψ : FundamentalIdentityAlong 𝕂 ψ hψ) (hfinφ : FiniteAlong 𝕂 φ)
      (hNφ : NormFormulaAlong 𝕂 φ hfinφ)
      (n : ℕ) (x y : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n (Pic0.correspondence φ ψ hφ hψ hFIφ hfinψ hNψ x) y
        = e n x (Pic0.correspondence ψ φ hψ hφ hFIψ hfinφ hNφ y))
    (he9 : ∀ (n : ℕ) (x y : JH M H), 0 < n → (n : ℤ) • x = 0 → (n : ℤ) • y = 0 →
      e n x y * e n y x = 1)
    (W : SemilinearAut 𝕂 (xHFunctionFieldBar M H))
    (hw1 : ∀ (ℓ : ℕ) [Fact ℓ.Prime]
      (hα : HeckeAlphaHBarIntegral 𝕂 M H ℓ) (hβ : HeckeBetaHBarIntegral 𝕂 M H ℓ)
      [HasPrincipalDivisors 𝕂 (laurentBaseChange 𝕂 (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
      (hFIβ : FundamentalIdentityAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ) hβ)
      (hfinα : FiniteAlong 𝕂 (heckeAlphaHBar 𝕂 M H ℓ))
      (hNα : NormFormulaAlong 𝕂 (heckeAlphaHBar 𝕂 M H ℓ) hfinα)
      (hFIα : FundamentalIdentityAlong 𝕂 (heckeAlphaHBar 𝕂 M H ℓ) hα)
      (hfinβ : FiniteAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ))
      (hNβ : NormFormulaAlong 𝕂 (heckeBetaHBar 𝕂 M H ℓ) hfinβ)
      (x : JH M H),
      heckePic0HBarTranspose hα hβ hFIα hfinβ hNβ (W • x) = W • heckePic0HBar hα hβ hFIβ hfinα hNα x)
    (hw2 : ∀ (d : (ZMod M)ˣ) (x : JH M H), diamondHBar M H d (W • diamondHBar M H d x) = W • x)
    (hw3 : ∀ x : JH M H, W • (W • x) = x)
    (hw4 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring 𝕂), A.LiesOverPrime ℓ →
      ∀ σ : 𝕂 ≃ₐ[ℚ] 𝕂, A.IsFrobeniusAt σ ℓ → ∀ x : JH M H,
        W • (σ • x) = σ • diamondHBar M H
          (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)) (W • x))
    (hw5 : ∀ (σ : 𝕂 ≃ₐ[ℚ] 𝕂) (c : ℕ) (hc : c.Coprime M), (∀ ζ : 𝕂, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : JH M H, W • (σ • x) = σ • diamondHBar M H (ZMod.unitOfCoprime c hc) (W • x))
    (hχW : ∀ z : 𝕂, SemilinearAut.baseAut W z = z)
    (hdiv : ∀ u : JH M H, ∃ v : JH M H, ((p : ℕ) : ℤ) • v = u) :
    ∃ B : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JH M H)) →ₗ[ℚ_[p]]
        TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JH M H)) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
          (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JH M H))),
        B ((JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                heckeOperatorHAlong 𝕂 M H ℓ)).baseChange ℚ_[p] x) y =
          B x ((JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                heckeOperatorHAlong 𝕂 M H ℓ)).baseChange ℚ_[p] y)) ∧
      (∀ (d : (ZMod M)ˣ) (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JH M H))),
        B ((JH.tateEnd M H p (diamondHBar M H d)).baseChange ℚ_[p] x) y =
          B x ((JH.tateEnd M H p (diamondHBar M H d)).baseChange ℚ_[p] y)) ∧
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring 𝕂, A.LiesOverPrime ℓ →
          ∀ σ : 𝕂 ≃ₐ[ℚ] 𝕂, A.IsFrobeniusAt σ ℓ →
            ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JH M H)),
              B ((JH.tateEnd M H p (diamondHBar M H
                    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange
                  ℚ_[p] ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
                ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
              (ℓ : ℚ_[p]) * B x y) ∧
      (∀ (σ : 𝕂 ≃ₐ[ℚ] 𝕂) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : 𝕂, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (JH M H)),
            B ((JH.tateEnd M H p (diamondHBar M H (ZMod.unitOfCoprime c hc))).baseChange ℚ_[p]
                ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
              ((JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
            (((cyclotomicCharacter 𝕂 p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * B x y) := by
  have hWt : ∀ {m : ℤ} {v : JH M H}, m • v = 0 → m • (W • v) = 0 := fun {m v} hv => by
    rw [← SemilinearAut.smul_zsmul, hv]; exact smul_zero (A := JH M H) W
  refine (SimilitudeEngineH.assembleH (p := p) (J := JH M H)
    (fun (g : SemilinearAut 𝕂 (xHFunctionFieldBar M H)) (z : 𝕂) => SemilinearAut.baseAut g z)
    e he1 he2 he3 he4 he6 he7 he9 W hw3 hχW hdiv).elim fun B hB => ?_
  obtain ⟨hbal, halt, hnd, hsim, hsimu⟩ := hB
  refine ⟨B, ?_, ?_, halt, hnd, ?_, ?_⟩
  ·
    intro ℓ hℓ x y
    exact hbal _ (fun n u v hn hu hv => adjoint_T M H e W hin he8 hw1 hℓ n u v hn hu (hWt hv)) x y
  ·
    intro d x y
    exact hbal _ (fun n u v hn hu hv => adjoint_dia M H e W he7 hw2 d n u v hn hu (hWt hv)) x y
  ·
    intro ℓ hℓ hℓM hℓp A hA σ hσ x y
    exact simil M H W p B hsim (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
      hℓ hℓp A hA σ hσ (hw4 ℓ hℓ hℓM A hA σ hσ) x y
  ·
    intro σ c hc hσc x y
    exact simil_cyc M H W p B hsimu σ c hc (hw5 σ c hc hσc) x y

end KSimJH
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.KSimJH"

open AlgebraicCurve ModularCurve SimilitudeEngineH in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    ∃ B : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)) →ₗ[ℚ_[p]]
        TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)) →ₗ[ℚ_[p]] ℚ_[p],
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime)
          (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
        B ((ModularCurve.JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ)).baseChange ℚ_[p] x) y =
          B x ((ModularCurve.JH.tateEnd M H p
              (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
                ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ)).baseChange ℚ_[p] y)) ∧
      (∀ (d : (ZMod M)ˣ) (x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H))),
        B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H d)).baseChange ℚ_[p] x) y =
          B x ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H d)).baseChange ℚ_[p] y)) ∧
      (∀ v, B v v = 0) ∧
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ≠ p →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
            ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)),
              B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H
                    (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)))).baseChange
                  ℚ_[p] ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
                ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
              (ℓ : ℚ_[p]) * B x y) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
          ∀ x y : TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)),
            B ((ModularCurve.JH.tateEnd M H p (ModularCurve.diamondHBar M H
                  (ZMod.unitOfCoprime c hc))).baseChange ℚ_[p]
                ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] x))
              ((ModularCurve.JH.tateGaloisRep M H p σ).baseChange ℚ_[p] y) =
            (((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) *
              B x y) := by
  have hp : Fact p.Prime := inferInstance

  have hfg := KSimJH.presentation_bot M H
  haveI : IsCurveOver (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) := by
    obtain ⟨x, hx, hfd⟩ := hfg
    exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField hx hfd

  refine (AlgebraicCurve.Pic0.exists_antisymmWeilPairing.{0, 0, 0} (AlgebraicClosure ℚ)
    (xHFunctionFieldBar M H) hfg).elim fun e he => ?_
  obtain ⟨he1, he2, he3, he4, -, he6, he7, he8, he9⟩ := he

  refine (ModularCurve.exists_frickeAlgEquiv_xHFunctionFieldBar_galois_smul M H).elim fun w hw => ?_
  obtain ⟨hw1, hw2, hw3, hw5⟩ := hw

  have hw4 : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          ∀ x : JH M H,
            SemilinearAut.ofAlgAut w • (σ • x)
              = σ • diamondHBar M H
                  (ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
                  (SemilinearAut.ofAlgAut w • x) := by
    intro ℓ hℓ hℓM A hA σ hσ x
    have hcop : M.Coprime ℓ := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM))
    exact hw5 σ ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)
      (fun ζ hζ => ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ ℓ M hA hσ hcop ζ hζ) x

  have hdiv : ∀ u : JH M H, ∃ v : JH M H, ((p : ℕ) : ℤ) • v = u := fun u => by
    obtain ⟨v, hv⟩ := AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ)
      (xHFunctionFieldBar M H) hfg p hp.out.ne_zero u
    exact ⟨v, by rw [natCast_zsmul, hv]⟩
  exact KSimJH.core M H p hin e he1 he2 he3 he4 he6 he7 he8 he9 (SemilinearAut.ofAlgAut w)
    hw1 hw2 hw3 hw4 (fun σ c hc hσc x => hw5 σ c hc hσc x) (fun _ => rfl) hdiv

end
p2m_reactivate "P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH.LevelPairing P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.SimilitudeEngineH P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH.KSimJH"

end S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH
end P2MW
export P2MW.S_ModularCurve_exists_diamondCyclotomicSimilitudePairing_rationalTateModule_jH (solution)
