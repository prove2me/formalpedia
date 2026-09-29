-- Prove2me | solution 1 for ModularCurve.exists_bilinForm_tateModule_nondegenerate_hecke_galois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7c9575f3-844a-5583-90bf-7c660b270c42

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_JZeroTateModule
import Theorems.Thm_ModularCurve_exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat
import Theorems.Thm_ModularCurve_exists_tateModule_apply_eq_of_pow_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bilinForm_tateModule_nondegenerate_hecke_galois
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"
p2m_attr_erase "simp" "ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateMap_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply HahnSeries.ramScale_apply"

set_option autoImplicit false

open ModularCurve

noncomputable section

namespace PairTProof

section Roots

variable {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem exists_isPrimitiveRoot_prime : ∃ z : L, IsPrimitiveRoot z ℓ := by
  have hdeg : (Polynomial.cyclotomic ℓ L).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr hℓ.out.pos).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  haveI : NeZero ((ℓ : ℕ) : L) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  exact ⟨z, Polynomial.isRoot_cyclotomic_iff.mp hz⟩

theorem exists_pow_eq_isPrimitiveRoot_succ (k : ℕ) (z : L) (hz : IsPrimitiveRoot z (ℓ ^ (k + 1))) :
    ∃ w : L, w ^ ℓ = z ∧ IsPrimitiveRoot w (ℓ ^ (k + 1 + 1)) := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z hℓ.out.pos
  refine ⟨w, hw, ?_⟩
  have h1 : w ^ ℓ ^ (k + 1 + 1) = 1 := by
    rw [pow_succ' ℓ (k + 1), pow_mul, hw]
    exact hz.pow_eq_one
  have h2 : ¬ w ^ ℓ ^ (k + 1) = 1 := by
    intro h
    rw [pow_succ' ℓ k, pow_mul, hw] at h
    have hdvd := (hz.pow_eq_one_iff_dvd (ℓ ^ k)).mp h
    have hlt : ℓ ^ k < ℓ ^ (k + 1) := Nat.pow_lt_pow_right hℓ.out.one_lt (Nat.lt_succ_self k)
    exact absurd (Nat.le_of_dvd (pow_pos hℓ.out.pos k) hdvd) (not_le.mpr hlt)
  have hord := orderOf_eq_prime_pow h2 h1
  rw [← hord]
  exact IsPrimitiveRoot.orderOf w

theorem exists_compatible_primitiveRoots :
    ∃ ζ : ℕ → L, (∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) ∧ ∀ k, ζ (k + 1) ^ ℓ = ζ k := by
  classical
  obtain ⟨z1, hz1⟩ := exists_isPrimitiveRoot_prime (L := L) ℓ
  have hz1' : IsPrimitiveRoot z1 (ℓ ^ (0 + 1)) := by simpa using hz1
  let g : (k : ℕ) → {z : L // IsPrimitiveRoot z (ℓ ^ (k + 1))} := fun k =>
    Nat.rec (motive := fun k => {z : L // IsPrimitiveRoot z (ℓ ^ (k + 1))}) ⟨z1, hz1'⟩
      (fun k zk => ⟨Classical.choose (exists_pow_eq_isPrimitiveRoot_succ ℓ k zk.1 zk.2),
        (Classical.choose_spec (exists_pow_eq_isPrimitiveRoot_succ ℓ k zk.1 zk.2)).2⟩) k
  have hg : ∀ k, (g (k + 1)).1 ^ ℓ = (g k).1 := fun k =>
    (Classical.choose_spec (exists_pow_eq_isPrimitiveRoot_succ ℓ k (g k).1 (g k).2)).1
  refine ⟨fun k => if k = 0 then 1 else (g (k - 1)).1, fun k => ?_, fun k => ?_⟩
  · rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one]
      exact (g k).2
  · rcases k with _ | k
    · simp only [Nat.zero_add, one_ne_zero, ↓reduceIte, Nat.sub_self]
      have := (g 0).2.pow_eq_one
      simpa using this
    · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, Nat.add_sub_cancel]
      exact hg k

end Roots

section DLog

variable {L : Type*} [Field L] {n : ℕ} [NeZero n] {ζ : L}

def zetaUnit (hζ : IsPrimitiveRoot ζ n) : Lˣ := (hζ.isUnit (NeZero.ne n)).unit

theorem coe_zetaUnit (hζ : IsPrimitiveRoot ζ n) : ((zetaUnit hζ : Lˣ) : L) = ζ := IsUnit.unit_spec _

theorem zetaUnit_isPrimitiveRoot (hζ : IsPrimitiveRoot ζ n) : IsPrimitiveRoot (zetaUnit hζ) n :=
  IsPrimitiveRoot.coe_units_iff.mp (by rw [coe_zetaUnit]; exact hζ)

theorem ne_zero_of_pow_eq_one {u : L} (hu : u ^ n = 1) : u ≠ 0 := by
  intro h
  rw [h, zero_pow (NeZero.ne n)] at hu
  exact zero_ne_one hu

theorem mk0_mem_zpowers (hζ : IsPrimitiveRoot ζ n) {u : L} (hu : u ^ n = 1) :
    Units.mk0 u (ne_zero_of_pow_eq_one hu) ∈ Subgroup.zpowers (zetaUnit hζ) := by
  rw [(zetaUnit_isPrimitiveRoot hζ).zpowers_eq]
  exact (mem_rootsOfUnity n _).mpr (Units.ext (by simp [hu]))

def dlog (hζ : IsPrimitiveRoot ζ n) (u : L) (hu : u ^ n = 1) : ZMod n :=
  (zetaUnit_isPrimitiveRoot hζ).zmodEquivZPowers.symm
    (Additive.ofMul ⟨Units.mk0 u (ne_zero_of_pow_eq_one hu), mk0_mem_zpowers hζ hu⟩)

theorem dlog_unique (hζ : IsPrimitiveRoot ζ n) {u : L} (hu : u ^ n = 1) (m : ℕ) (hm : ζ ^ m = u) :
    dlog hζ u hu = m := by
  unfold dlog
  rw [AddEquiv.symm_apply_eq, IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [Units.val_pow_eq_pow_val, coe_zetaUnit, hm]

theorem pow_dlog (hζ : IsPrimitiveRoot ζ n) {u : L} (hu : u ^ n = 1) : ζ ^ (dlog hζ u hu).val = u := by
  have h := (zetaUnit_isPrimitiveRoot hζ).zmodEquivZPowers.apply_symm_apply
    (Additive.ofMul ⟨Units.mk0 u (ne_zero_of_pow_eq_one hu), mk0_mem_zpowers hζ hu⟩)
  change (zetaUnit_isPrimitiveRoot hζ).zmodEquivZPowers (dlog hζ u hu) = _ at h
  rw [← ZMod.natCast_zmod_val (dlog hζ u hu), IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat] at h
  have h' := congrArg (fun z : Additive ↥(Subgroup.zpowers (zetaUnit hζ)) =>
    ((Additive.toMul z : ↥(Subgroup.zpowers (zetaUnit hζ))) : Lˣ).val) h
  simpa [Units.val_pow_eq_pow_val, coe_zetaUnit] using h'

theorem dlog_mul (hζ : IsPrimitiveRoot ζ n) {u v : L} (hu : u ^ n = 1) (hv : v ^ n = 1) (huv : (u * v) ^ n = 1) :
    dlog hζ (u * v) huv = dlog hζ u hu + dlog hζ v hv := by
  rw [← ZMod.natCast_zmod_val (dlog hζ u hu), ← ZMod.natCast_zmod_val (dlog hζ v hv), ← Nat.cast_add]
  apply dlog_unique
  rw [pow_add, pow_dlog, pow_dlog]

theorem dlog_pow (hζ : IsPrimitiveRoot ζ n) {u : L} (hu : u ^ n = 1) (m : ℕ) (hum : (u ^ m) ^ n = 1) :
    dlog hζ (u ^ m) hum = (m : ZMod n) * dlog hζ u hu := by
  rw [← ZMod.natCast_zmod_val (dlog hζ u hu), ← Nat.cast_mul]
  apply dlog_unique
  rw [mul_comm, pow_mul, pow_dlog]

theorem eq_one_of_dlog_eq_zero (hζ : IsPrimitiveRoot ζ n) {u : L} (hu : u ^ n = 1) (h : dlog hζ u hu = 0) : u = 1 := by
  rw [← pow_dlog hζ hu, h, ZMod.val_zero, pow_zero]

theorem dlog_congr (hζ : IsPrimitiveRoot ζ n) {u v : L} (hu : u ^ n = 1) (hv : v ^ n = 1) (h : u = v) :
    dlog hζ u hu = dlog hζ v hv := by
  subst h; rfl

theorem cast_dlog_eq {ℓ : ℕ} {ζ' : L} [NeZero (n * ℓ)] (hζ : IsPrimitiveRoot ζ n) (hζ' : IsPrimitiveRoot ζ' (n * ℓ))
    (hpow : ζ' ^ ℓ = ζ) {v : L} (hv : v ^ (n * ℓ) = 1) (hvℓ : (v ^ ℓ) ^ n = 1) :
    (ZMod.castHom (dvd_mul_right n ℓ) (ZMod n)) (dlog hζ' v hv) = dlog hζ (v ^ ℓ) hvℓ := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val]
  symm
  apply dlog_unique
  rw [← hpow, ← pow_mul, mul_comm, pow_mul, pow_dlog]

end DLog

section Main

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

scoped instance neZero_pow (k : ℕ) : NeZero (ℓ ^ k) := ⟨pow_ne_zero k hℓ.out.ne_zero⟩

theorem torsion_nsmul (x : TateModule ℓ (JZero p)) (k : ℕ) : ℓ ^ k • (x : ℕ → JZero p) k = 0 := by
  have := TateModule.torsion x k
  rwa [natCast_zsmul] at this

theorem compat_nsmul (x : TateModule ℓ (JZero p)) (k : ℕ) :
    ℓ • (x : ℕ → JZero p) (k + 1) = (x : ℕ → JZero p) k := by
  have := TateModule.compat x k
  rwa [natCast_zsmul] at this

theorem nsmul_torsion {x : JZero p} {k : ℕ} (hx : ℓ ^ k • x = 0) (m : ℕ) : ℓ ^ k • (m • x) = 0 := by
  rw [smul_comm, hx, smul_zero]

variable (B : ℕ → JZero p → JZero p → AlgebraicClosure ℚ)

def C1 : Prop := ∀ k (x y : JZero p), ℓ ^ k • x = 0 → ℓ ^ k • y = 0 → B k x y ^ (ℓ ^ k) = 1
def C2 : Prop := ∀ k (x x' y : JZero p), ℓ ^ k • x = 0 → ℓ ^ k • x' = 0 → ℓ ^ k • y = 0 → B k (x + x') y = B k x y * B k x' y
def C3 : Prop := ∀ k (x y y' : JZero p), ℓ ^ k • x = 0 → ℓ ^ k • y = 0 → ℓ ^ k • y' = 0 → B k x (y + y') = B k x y * B k x y'
def C8 : Prop := ∀ k (x y : JZero p), ℓ ^ (k + 1) • x = 0 → ℓ ^ k • y = 0 → B (k + 1) x y = B k (ℓ • x) y

variable {p ℓ B}

theorem B_zero_right (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (k : ℕ) (x : JZero p) (hx : ℓ ^ k • x = 0) : B k x 0 = 1 := by
  have hm := h3 k x 0 0 hx (smul_zero _) (smul_zero _)
  rw [add_zero] at hm
  have hne : B k x 0 ≠ 0 := ne_zero_of_pow_eq_one (n := ℓ ^ k) (h1 k x 0 hx (smul_zero _))
  have hz : B k x 0 * (B k x 0 - 1) = 0 := by rw [mul_sub, mul_one, ← hm, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

theorem B_zero_left (h1 : C1 p ℓ B) (h2 : C2 p ℓ B) (k : ℕ) (y : JZero p) (hy : ℓ ^ k • y = 0) : B k 0 y = 1 := by
  have hm := h2 k 0 0 y (smul_zero _) (smul_zero _) hy
  rw [add_zero] at hm
  have hne : B k 0 y ≠ 0 := ne_zero_of_pow_eq_one (n := ℓ ^ k) (h1 k 0 y (smul_zero _) hy)
  have hz : B k 0 y * (B k 0 y - 1) = 0 := by rw [mul_sub, mul_one, ← hm, sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h hne
  · exact sub_eq_zero.mp h

theorem B_nsmul_right (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (k : ℕ) (x y : JZero p) (hx : ℓ ^ k • x = 0) (hy : ℓ ^ k • y = 0)
    (m : ℕ) : B k x (m • y) = B k x y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, B_zero_right h1 h3 k x hx]
  | succ m ih => rw [succ_nsmul, h3 k x (m • y) y hx (nsmul_torsion p ℓ hy m) hy, ih, pow_succ]

theorem B_nsmul_left (h1 : C1 p ℓ B) (h2 : C2 p ℓ B) (k : ℕ) (x y : JZero p) (hx : ℓ ^ k • x = 0) (hy : ℓ ^ k • y = 0)
    (m : ℕ) : B k (m • x) y = B k x y ^ m := by
  induction m with
  | zero => rw [zero_nsmul, pow_zero, B_zero_left h1 h2 k y hy]
  | succ m ih => rw [succ_nsmul, h2 k (m • x) x y (nsmul_torsion p ℓ hx m) hx hy, ih, pow_succ]

theorem B_pow (h1 : C1 p ℓ B) (k : ℕ) (x y : TateModule ℓ (JZero p)) :
    B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ (ℓ ^ k) = 1 :=
  h1 k _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ y k)

theorem B_succ_pow (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) (k : ℕ) (x y : TateModule ℓ (JZero p)) :
    B (k + 1) ((x : ℕ → JZero p) (k + 1)) ((y : ℕ → JZero p) (k + 1)) ^ ℓ =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) := by
  rw [← B_nsmul_right h1 h3 (k + 1) _ _ (torsion_nsmul p ℓ x (k + 1)) (torsion_nsmul p ℓ y (k + 1)) ℓ,
    compat_nsmul p ℓ y k, h8 k ((x : ℕ → JZero p) (k + 1)) ((y : ℕ → JZero p) k) (torsion_nsmul p ℓ x (k + 1))
      (torsion_nsmul p ℓ y k), compat_nsmul p ℓ x k]

theorem B_add_pow (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) (k d : ℕ) (x y : TateModule ℓ (JZero p)) :
    B (k + d) ((x : ℕ → JZero p) (k + d)) ((y : ℕ → JZero p) (k + d)) ^ (ℓ ^ d) =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) := by
  induction d with
  | zero => rw [pow_zero, pow_one, Nat.add_zero]
  | succ d ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, B_succ_pow h1 h3 h8 (k + d) x y, ih]

variable {ζ : ℕ → AlgebraicClosure ℚ}

theorem zeta_add_pow (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k) (k d : ℕ) : ζ (k + d) ^ (ℓ ^ d) = ζ k := by
  induction d with
  | zero => rw [pow_zero, pow_one, Nat.add_zero]
  | succ d ih => rw [pow_succ', pow_mul, ← Nat.add_assoc, hζc (k + d), ih]

def A (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (h1 : C1 p ℓ B) (k : ℕ) (x y : TateModule ℓ (JZero p)) : ZMod (ℓ ^ k) :=
  dlog (hζ k) (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k)) (B_pow h1 k x y)

theorem A_def (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (h1 : C1 p ℓ B) (k : ℕ) (x y : TateModule ℓ (JZero p)) :
    A hζ h1 k x y = dlog (hζ k) (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k)) (B_pow h1 k x y) := rfl

theorem pow_A (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (h1 : C1 p ℓ B) (k : ℕ) (x y : TateModule ℓ (JZero p)) :
    ζ k ^ (A hζ h1 k x y).val = B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) :=
  pow_dlog (hζ k) (B_pow h1 k x y)

theorem cast_A (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) (k d : ℕ) (x y : TateModule ℓ (JZero p)) :
    (ZMod.castHom (pow_dvd_pow ℓ (Nat.le_add_right k d)) (ZMod (ℓ ^ k))) (A hζ h1 (k + d) x y) = A hζ h1 k x y := by
  rw [ZMod.castHom_apply, ← ZMod.natCast_val, A_def hζ h1 k]
  symm
  apply dlog_unique
  rw [← zeta_add_pow hζc k d, ← pow_mul, mul_comm, pow_mul, pow_A, B_add_pow h1 h3 h8]

theorem cast_A_of_le (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) {k1 k2 : ℕ} (hk : k1 ≤ k2) (x y : TateModule ℓ (JZero p)) :
    (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))) (A hζ h1 k2 x y) = A hζ h1 k1 x y := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact cast_A hζ hζc h1 h3 h8 k1 d x y

def fam (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (h1 : C1 p ℓ B) (x y : TateModule ℓ (JZero p)) (k : ℕ) :
    Polynomial ℤ →+* ZMod (ℓ ^ k) :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod (ℓ ^ k))) (A hζ h1 k x y)

theorem fam_compat (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) (x y : TateModule ℓ (JZero p))
    (k1 k2 : ℕ) (hk : k1 ≤ k2) :
    (ZMod.castHom (pow_dvd_pow ℓ hk) (ZMod (ℓ ^ k1))).comp (fam hζ h1 x y k2) = fam hζ h1 x y k1 := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [fam]
  · simp only [fam, RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    exact cast_A_of_le hζ hζc h1 h3 h8 hk x y

private def _root_.PairTProof.val (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) (x y : TateModule ℓ (JZero p)) : ℤ_[ℓ] :=
  PadicInt.lift (fam_compat hζ hζc h1 h3 h8 x y) Polynomial.X

p2m_export "PairTProof" "val"
theorem toZModPow_val (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
    (h1 : C1 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B) (k : ℕ) (x y : TateModule ℓ (JZero p)) :
    PadicInt.toZModPow k (val hζ hζc h1 h3 h8 x y) = A hζ h1 k x y := by
  unfold val
  rw [← RingHom.comp_apply, PadicInt.lift_spec]
  simp [fam]

theorem toZModPow_eq_appr' (k : ℕ) (c : ℤ_[ℓ]) : PadicInt.toZModPow k c = ((c.appr k : ℕ) : ZMod (ℓ ^ k)) := rfl

section Lin
variable (hζ : ∀ k, IsPrimitiveRoot (ζ k) (ℓ ^ k)) (hζc : ∀ k, ζ (k + 1) ^ ℓ = ζ k)
  (h1 : C1 p ℓ B) (h2 : C2 p ℓ B) (h3 : C3 p ℓ B) (h8 : C8 p ℓ B)
include hζ hζc h1 h2 h3 h8

theorem val_add_left (x x' y : TateModule ℓ (JZero p)) :
    val hζ hζc h1 h3 h8 (x + x') y = val hζ hζc h1 h3 h8 x y + val hζ hζc h1 h3 h8 x' y := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [map_add, toZModPow_val, toZModPow_val, toZModPow_val, A_def, A_def, A_def]
  have e : B k (((x + x' : TateModule ℓ (JZero p)) : ℕ → JZero p) k) ((y : ℕ → JZero p) k) =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) * B k ((x' : ℕ → JZero p) k) ((y : ℕ → JZero p) k) :=
    h2 k _ _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ x' k) (torsion_nsmul p ℓ y k)
  have hprod : (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) * B k ((x' : ℕ → JZero p) k) ((y : ℕ → JZero p) k)) ^ (ℓ ^ k) = 1 := by
    rw [mul_pow, B_pow h1, B_pow h1, one_mul]
  rw [dlog_congr (hζ k) _ hprod e, dlog_mul (hζ k) (B_pow h1 k x y) (B_pow h1 k x' y)]

theorem val_add_right (x y y' : TateModule ℓ (JZero p)) :
    val hζ hζc h1 h3 h8 x (y + y') = val hζ hζc h1 h3 h8 x y + val hζ hζc h1 h3 h8 x y' := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [map_add, toZModPow_val, toZModPow_val, toZModPow_val, A_def, A_def, A_def]
  have e : B k ((x : ℕ → JZero p) k) (((y + y' : TateModule ℓ (JZero p)) : ℕ → JZero p) k) =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) * B k ((x : ℕ → JZero p) k) ((y' : ℕ → JZero p) k) :=
    h3 k _ _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ y k) (torsion_nsmul p ℓ y' k)
  have hprod : (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) * B k ((x : ℕ → JZero p) k) ((y' : ℕ → JZero p) k)) ^ (ℓ ^ k) = 1 := by
    rw [mul_pow, B_pow h1, B_pow h1, one_mul]
  rw [dlog_congr (hζ k) _ hprod e, dlog_mul (hζ k) (B_pow h1 k x y) (B_pow h1 k x y')]

theorem val_smul_left (c : ℤ_[ℓ]) (x y : TateModule ℓ (JZero p)) :
    val hζ hζc h1 h3 h8 (c • x) y = c • val hζ hζc h1 h3 h8 x y := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [smul_eq_mul, map_mul, toZModPow_val, toZModPow_val, A_def, A_def, toZModPow_eq_appr']
  have e : B k (((c • x : TateModule ℓ (JZero p)) : ℕ → JZero p) k) ((y : ℕ → JZero p) k) =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ (c.appr k) := by
    rw [TateModule.smul_apply, natCast_zsmul]
    exact B_nsmul_left h1 h2 k _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ y k) (c.appr k)
  have hpow' : (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ (c.appr k)) ^ (ℓ ^ k) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, B_pow h1, one_pow]
  rw [dlog_congr (hζ k) _ hpow' e, dlog_pow (hζ k) (B_pow h1 k x y)]

theorem val_smul_right (c : ℤ_[ℓ]) (x y : TateModule ℓ (JZero p)) :
    val hζ hζc h1 h3 h8 x (c • y) = c • val hζ hζc h1 h3 h8 x y := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [smul_eq_mul, map_mul, toZModPow_val, toZModPow_val, A_def, A_def, toZModPow_eq_appr']
  have e : B k ((x : ℕ → JZero p) k) (((c • y : TateModule ℓ (JZero p)) : ℕ → JZero p) k) =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ (c.appr k) := by
    rw [TateModule.smul_apply, natCast_zsmul]
    exact B_nsmul_right h1 h3 k _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ y k) (c.appr k)
  have hpow' : (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ (c.appr k)) ^ (ℓ ^ k) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, B_pow h1, one_pow]
  rw [dlog_congr (hζ k) _ hpow' e, dlog_pow (hζ k) (B_pow h1 k x y)]

def Bf : TateModule ℓ (JZero p) →ₗ[ℤ_[ℓ]] TateModule ℓ (JZero p) →ₗ[ℤ_[ℓ]] ℤ_[ℓ] :=
  LinearMap.mk₂ ℤ_[ℓ] (val hζ hζc h1 h3 h8) (val_add_left hζ hζc h1 h2 h3 h8) (val_smul_left hζ hζc h1 h2 h3 h8)
    (val_add_right hζ hζc h1 h2 h3 h8) (val_smul_right hζ hζc h1 h2 h3 h8)

theorem Bf_apply (x y : TateModule ℓ (JZero p)) : Bf hζ hζc h1 h2 h3 h8 x y = val hζ hζc h1 h3 h8 x y := rfl

theorem toZModPow_Bf (k : ℕ) (x y : TateModule ℓ (JZero p)) :
    PadicInt.toZModPow k (Bf hζ hζc h1 h2 h3 h8 x y) = A hζ h1 k x y :=
  toZModPow_val hζ hζc h1 h3 h8 k x y

theorem Bf_nondeg_left
    (h4 : ∀ k (x : JZero p), ℓ ^ k • x = 0 → (∀ y : JZero p, ℓ ^ k • y = 0 → B k x y = 1) → x = 0)
    (x : TateModule ℓ (JZero p)) (hx : ∀ y, Bf hζ hζc h1 h2 h3 h8 x y = 0) : x = 0 := by
  apply Subtype.ext
  funext k
  show (x : ℕ → JZero p) k = 0
  refine h4 k _ (torsion_nsmul p ℓ x k) fun y' hy' => ?_
  obtain ⟨s, hs⟩ := ModularCurve.exists_tateModule_apply_eq_of_pow_smul_eq_zero p ℓ k y' hy'
  have h0 : A hζ h1 k x s = 0 := by rw [← toZModPow_Bf hζ hζc h1 h2 h3 h8, hx s, map_zero]
  have := eq_one_of_dlog_eq_zero (hζ k) (B_pow h1 k x s) h0
  rwa [hs] at this

theorem Bf_nondeg_right
    (h7 : ∀ k (y : JZero p), ℓ ^ k • y = 0 → (∀ x : JZero p, ℓ ^ k • x = 0 → B k x y = 1) → y = 0)
    (y : TateModule ℓ (JZero p)) (hy : ∀ x, Bf hζ hζc h1 h2 h3 h8 x y = 0) : y = 0 := by
  apply Subtype.ext
  funext k
  show (y : ℕ → JZero p) k = 0
  refine h7 k _ (torsion_nsmul p ℓ y k) fun x' hx' => ?_
  obtain ⟨s, hs⟩ := ModularCurve.exists_tateModule_apply_eq_of_pow_smul_eq_zero p ℓ k x' hx'
  have h0 : A hζ h1 k s y = 0 := by rw [← toZModPow_Bf hζ hζc h1 h2 h3 h8, hy s, map_zero]
  have := eq_one_of_dlog_eq_zero (hζ k) (B_pow h1 k s y) h0
  rwa [hs] at this

set_option maxHeartbeats 3200000 in
theorem Bf_hecke [Module HeckeAlg (JZero p)]
    (h6 : ∀ k (t : HeckeAlg) (x y : JZero p), ℓ ^ k • x = 0 → ℓ ^ k • y = 0 → B k (t • x) y = B k x (t • y))
    (t : HeckeAlg) (x y : TateModule ℓ (JZero p)) :
    Bf hζ hζc h1 h2 h3 h8 (tateHeckeRep ℓ (JZero p) t x) y = Bf hζ hζc h1 h2 h3 h8 x (tateHeckeRep ℓ (JZero p) t y) := by
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  rw [toZModPow_Bf, toZModPow_Bf, A_def, A_def]
  have e : B k (((tateHeckeRep ℓ (JZero p) t x : TateModule ℓ (JZero p)) : ℕ → JZero p) k) ((y : ℕ → JZero p) k) =
      B k ((x : ℕ → JZero p) k) (((tateHeckeRep ℓ (JZero p) t y : TateModule ℓ (JZero p)) : ℕ → JZero p) k) := by
    rw [coe_tateHeckeRep_apply_apply, coe_tateHeckeRep_apply_apply]
    exact h6 k t _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ y k)
  exact dlog_congr (hζ k) _ _ e

set_option maxHeartbeats 3200000 in
theorem Bf_galois
    (h5 : ∀ k (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x y : JZero p), ℓ ^ k • x = 0 → ℓ ^ k • y = 0 →
      B k (σ • x) (σ • y) = σ (B k x y))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k nk : ℕ)
    (hσ : ∀ z : AlgebraicClosure ℚ, z ^ (ℓ ^ k) = 1 → σ z = z ^ nk) (x y : TateModule ℓ (JZero p)) :
    Bf hζ hζc h1 h2 h3 h8 (TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
        (TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y)
      - (nk : ℤ_[ℓ]) * Bf hζ hζc h1 h2 h3 h8 x y ∈ Ideal.span {((ℓ : ℤ_[ℓ]) ^ k)} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_mul, map_natCast, toZModPow_Bf, toZModPow_Bf, A_def, A_def]
  have e : B k (((TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x : TateModule ℓ (JZero p)) : ℕ → JZero p) k)
        (((TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y : TateModule ℓ (JZero p)) : ℕ → JZero p) k) =
      B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ nk := by
    rw [TateModule.rep_apply, TateModule.rep_apply, h5 k σ _ _ (torsion_nsmul p ℓ x k) (torsion_nsmul p ℓ y k)]
    exact hσ _ (B_pow h1 k x y)
  have hpow' : (B k ((x : ℕ → JZero p) k) ((y : ℕ → JZero p) k) ^ nk) ^ (ℓ ^ k) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, B_pow h1, one_pow]
  rw [dlog_congr (hζ k) _ hpow' e, dlog_pow (hζ k) (B_pow h1 k x y), sub_self]

end Lin

end Main

end PairTProof
p2m_reactivate "P2MW.S_ModularCurve_exists_bilinForm_tateModule_nondegenerate_hecke_galois.PairTProof"

set_option maxHeartbeats 6400000 in
open PairTProof in
theorem solution
    (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] :
    letI := heckeModuleBar p
    ∃ Bf : TateModule ℓ (JZero p) →ₗ[ℤ_[ℓ]] TateModule ℓ (JZero p) →ₗ[ℤ_[ℓ]] ℤ_[ℓ],
      (∀ x, (∀ y, Bf x y = 0) → x = 0) ∧ (∀ y, (∀ x, Bf x y = 0) → y = 0) ∧
      (∀ (t : HeckeAlg) (x y : TateModule ℓ (JZero p)),
        Bf (tateHeckeRep ℓ (JZero p) t x) y = Bf x (tateHeckeRep ℓ (JZero p) t y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (k nk : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ (ℓ ^ k) = 1 → σ ζ = ζ ^ nk) →
        ∀ x y : TateModule ℓ (JZero p),
          Bf (TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x)
              (TateModule.rep ℓ (JZero p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ y)
            - (nk : ℤ_[ℓ]) * Bf x y ∈ Ideal.span {((ℓ : ℤ_[ℓ]) ^ k)}) := by
  letI := heckeModuleBar p
  have hℓ : Fact ℓ.Prime := inferInstance
  obtain ⟨B, hB⟩ := ModularCurve.exists_pairing_family_pow_nsmul_eq_zero_galois_hecke_compat p ℓ hℓ.out.ne_zero
  obtain ⟨ζ, hζ, hζc⟩ := exists_compatible_primitiveRoots (L := AlgebraicClosure ℚ) ℓ
  have h1 : C1 p ℓ B := fun k => (hB k).1
  have h2 : C2 p ℓ B := fun k => (hB k).2.1
  have h3 : C3 p ℓ B := fun k => (hB k).2.2.1
  have h4 := fun k => (hB k).2.2.2.1
  have h5 := fun k => (hB k).2.2.2.2.1
  have h6 := fun k => (hB k).2.2.2.2.2.1
  have h7 := fun k => (hB k).2.2.2.2.2.2.1
  have h8 : C8 p ℓ B := fun k => (hB k).2.2.2.2.2.2.2.1
  exact ⟨Bf hζ hζc h1 h2 h3 h8, Bf_nondeg_left hζ hζc h1 h2 h3 h8 h4, Bf_nondeg_right hζ hζc h1 h2 h3 h8 h7,
    Bf_hecke hζ hζc h1 h2 h3 h8 h6, Bf_galois hζ hζc h1 h2 h3 h8 h5⟩

end
end S_ModularCurve_exists_bilinForm_tateModule_nondegenerate_hecke_galois
end P2MW
export P2MW.S_ModularCurve_exists_bilinForm_tateModule_nondegenerate_hecke_galois (solution)
