-- Prove2me | solution 1 for ModularCurve.exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bf26301c-f540-55eb-9302-9cd0d462a4d6

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC"
p2m_attr_erase "instance" "AlgebraicCurve.CellDissection.decEqE ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left ModularCurve.jqNModC_one CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11"
p2m_attr_erase "simp" "CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"

set_option autoImplicit false

open AlgebraicCurve ModularCurve

noncomputable section

namespace PairModP

local notation "ℚbar" => AlgebraicClosure ℚ

section Chi

variable {p : ℕ} [Fact p.Prime] {ζ : ℚbar}

def chi (ζ : ℚbar) (a : ZMod p) : ℚbar := ζ ^ a.val

omit [Fact p.Prime] in
theorem pow_mod (hζ : ζ ^ p = 1) (n : ℕ) : ζ ^ (n % p) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p]
  rw [pow_add, pow_mul, hζ, one_pow, mul_one]

theorem chi_zero : chi ζ (0 : ZMod p) = 1 := by
  rw [chi, ZMod.val_zero, pow_zero]

theorem chi_add (hζ : IsPrimitiveRoot ζ p) (a b : ZMod p) : chi ζ (a + b) = chi ζ a * chi ζ b := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [chi, chi, chi, ← pow_add, ZMod.val_add, pow_mod hζ.pow_eq_one]

theorem chi_natCast_mul (hζ : IsPrimitiveRoot ζ p) (c : ℕ) (a : ZMod p) :
    chi ζ ((c : ZMod p) * a) = ζ ^ (c * a.val) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [chi, ZMod.val_mul, ZMod.val_natCast, pow_mod hζ.pow_eq_one, ← pow_mod hζ.pow_eq_one,
    Nat.mod_mul_mod, pow_mod hζ.pow_eq_one]

theorem chi_injective (hζ : IsPrimitiveRoot ζ p) : Function.Injective (chi ζ : ZMod p → ℚbar) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro a b h
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

theorem exists_chi_eq (hζ : IsPrimitiveRoot ζ p) {u : ℚbar} (hu : u ^ p = 1) : ∃ a : ZMod p, chi ζ a = u := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨i, hi, e⟩ := hζ.eq_pow_of_pow_eq_one hu
  exact ⟨(i : ZMod p), by rw [chi, ZMod.val_natCast, Nat.mod_eq_of_lt hi]; exact e⟩

end Chi

section Log

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]

abbrev T : Type _ := ↥(Pic0.torsion ℚbar (xHFunctionFieldBar M H) p)

variable {M H p}

omit [NeZero M] [Fact p.Prime] in
theorem nsmul_coe (x : T M H p) : p • (x : JH M H) = 0 := by
  rw [← natCast_zsmul]
  exact Pic0.mem_torsion.mp x.2

omit [NeZero M] [Fact p.Prime] in
theorem mem_of_nsmul {y : JH M H} (hy : p • y = 0) : y ∈ Pic0.torsion ℚbar (xHFunctionFieldBar M H) p :=
  Pic0.mem_torsion.mpr (by rw [natCast_zsmul]; exact hy)

variable {ζ : ℚbar} (hζ : IsPrimitiveRoot ζ p)
  (B : JH M H → JH M H → ℚbar)
  (hB1 : ∀ x y : JH M H, p • x = 0 → p • y = 0 → B x y ^ p = 1)

def blog (x y : T M H p) : ZMod p :=
  Classical.choose (exists_chi_eq hζ (hB1 x y (nsmul_coe x) (nsmul_coe y)))

omit [NeZero M] in
theorem chi_blog (x y : T M H p) : chi ζ (blog hζ B hB1 x y) = B x y :=
  Classical.choose_spec (exists_chi_eq hζ (hB1 x y (nsmul_coe x) (nsmul_coe y)))

variable
  (hBL : ∀ x x' y : JH M H, p • x = 0 → p • x' = 0 → p • y = 0 → B (x + x') y = B x y * B x' y)
  (hBR : ∀ x y y' : JH M H, p • x = 0 → p • y = 0 → p • y' = 0 → B x (y + y') = B x y * B x y')

omit [NeZero M] in
include hBL in
theorem blog_add_left (x x' y : T M H p) :
    blog hζ B hB1 (x + x') y = blog hζ B hB1 x y + blog hζ B hB1 x' y := by
  apply chi_injective hζ
  rw [chi_add hζ, chi_blog, chi_blog, chi_blog]
  exact hBL x x' y (nsmul_coe x) (nsmul_coe x') (nsmul_coe y)

omit [NeZero M] in
include hBR in
theorem blog_add_right (x y y' : T M H p) :
    blog hζ B hB1 x (y + y') = blog hζ B hB1 x y + blog hζ B hB1 x y' := by
  apply chi_injective hζ
  rw [chi_add hζ, chi_blog, chi_blog, chi_blog]
  exact hBR x y y' (nsmul_coe x) (nsmul_coe y) (nsmul_coe y')

def blogAdd : T M H p →+ T M H p →+ ZMod p :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => blog hζ B hB1 x y) (blog_add_right hζ B hB1 hBR x))
    (fun x x' => AddMonoidHom.ext fun y => blog_add_left hζ B hB1 hBL x x' y)

def bForm : LinearMap.BilinForm (ZMod p) (T M H p) :=
  (((AddMonoidHom.toZModLinearMapEquiv p).toAddMonoidHom).comp (blogAdd hζ B hB1 hBL hBR)).toZModLinearMap p

omit [NeZero M] in
theorem bForm_apply (x y : T M H p) : bForm hζ B hB1 hBL hBR x y = blog hζ B hB1 x y := rfl

omit [NeZero M] in
theorem chi_bForm (x y : T M H p) : chi ζ (bForm hζ B hB1 hBL hBR x y) = B x y :=
  chi_blog hζ B hB1 x y

theorem bForm_eq_zero_iff (x y : T M H p) : bForm hζ B hB1 hBL hBR x y = 0 ↔ B x y = 1 := by
  rw [← (chi_injective hζ).eq_iff, chi_bForm, chi_zero]

omit [NeZero M] in

theorem adj_genOpH
    (hBhecke : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (x y : JH M H), p • x = 0 → p • y = 0 →
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      B (heckeOperatorHAlong ℚbar M H ℓ x) y = B x (heckeOperatorHAlong ℚbar M H ℓ y))
    (hBdia : ∀ (d : (ZMod M)ˣ) (x y : JH M H), p • x = 0 → p • y = 0 →
      B (diamondHBar M H d x) y = B x (diamondHBar M H d y))
    (S : Set ℕ) (g : CohCarrier.Gen M S) (x y : T M H p) :
    B (genOpH M H S g (x : JH M H)) y = B x (genOpH M H S g (y : JH M H)) := by
  cases g with
  | T ℓ hℓ hℓS hℓM => exact hBhecke ℓ hℓ x y (nsmul_coe x) (nsmul_coe y)
  | U q hq hqM => exact hBhecke q hq x y (nsmul_coe x) (nsmul_coe y)
  | dia d => exact hBdia d x y (nsmul_coe x) (nsmul_coe y)

theorem mem_of_forall_bForm
    (hBann : ∀ A : AddSubgroup (JH M H), (∀ a ∈ A, p • a = 0) →
      ∀ x : JH M H, p • x = 0 →
        (∀ y : JH M H, p • y = 0 → (∀ a ∈ A, B a y = 1) → B x y = 1) → x ∈ A)
    (A : Submodule (ZMod p) (T M H p)) (x : T M H p)
    (hx : ∀ y : T M H p, (∀ a ∈ A, bForm hζ B hB1 hBL hBR a y = 0) → bForm hζ B hB1 hBL hBR x y = 0) :
    x ∈ A := by

  let A' : AddSubgroup (JH M H) :=
    { carrier := {z | ∃ a : T M H p, a ∈ A ∧ (a : JH M H) = z}
      zero_mem' := ⟨0, A.zero_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
        exact ⟨a + a', A.add_mem ha ha', rfl⟩
      neg_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, A.neg_mem ha, rfl⟩ }
  have hA' : ∀ a ∈ A', p • a = 0 := by
    rintro _ ⟨a, -, rfl⟩
    exact nsmul_coe a
  have hmem : (x : JH M H) ∈ A' := by
    apply hBann A' hA' x (nsmul_coe x)
    intro y hy hAy
    have h := hx ⟨y, mem_of_nsmul hy⟩ (fun a ha => by
      rw [bForm_eq_zero_iff]
      exact hAy a ⟨a, ha, rfl⟩)
    rwa [bForm_eq_zero_iff] at h
  obtain ⟨a, ha, hax⟩ := hmem
  have : a = x := Subtype.ext hax
  rw [← this]
  exact ha

end Log

end PairModP

end

open PairModP in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) :
    ∃ b : LinearMap.BilinForm (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p),
      (∀ x, (∀ y, b x y = 0) → x = 0) ∧ (∀ y, (∀ x, b x y = 0) → y = 0) ∧

      (∀ (g : CohCarrier.Gen M S) (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (x' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
        (y' : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (y : ModularCurve.JH M H) →
          b x' y = b x y') ∧

      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ (x y x' y' : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
          (x' : ModularCurve.JH M H) = ModularCurve.diamondHBar M H (ZMod.unitOfCoprime c hc) (σ • (x : ModularCurve.JH M H)) →
          (y' : ModularCurve.JH M H) = σ • (y : ModularCurve.JH M H) →
            b x' y' = (c : ZMod p) • b x y) ∧

      (∀ (A : Submodule (ZMod p) ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p))
        (x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (∀ y, (∀ a ∈ A, b a y = 0) → b x y = 0) → x ∈ A) := by
  have pp : p.Prime := Fact.out
  haveI : NeZero p := ⟨pp.ne_zero⟩
  haveI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr pp.ne_zero⟩

  refine (HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) p).elim fun ζ hζ => ?_
  refine (ModularCurve.exists_perfectPairing_nsmul_eq_zero_galois_heckeH_diamondH_forall_addSubgroup_eq_biannihilator
      M H p pp.ne_zero).elim fun B hB => ?_
  have hB1 := hB.1
  have hBL := hB.2.1
  have hBR := hB.2.2.1
  have hBndL := hB.2.2.2.1
  have hBgal := hB.2.2.2.2.1
  have hBhecke := hB.2.2.2.2.2.1
  have hBdia := hB.2.2.2.2.2.2.1
  have hBndR := hB.2.2.2.2.2.2.2.1
  have hBann := hB.2.2.2.2.2.2.2.2
  refine ⟨bForm hζ (B) hB1 hBL hBR, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    apply Subtype.ext
    apply hBndL x (nsmul_coe x)
    intro y hy
    have h := hx ⟨y, mem_of_nsmul hy⟩
    rwa [bForm_eq_zero_iff] at h
  ·
    intro y hy
    apply Subtype.ext
    apply hBndR y (nsmul_coe y)
    intro x hx
    have h := hy ⟨x, mem_of_nsmul hx⟩
    rwa [bForm_eq_zero_iff] at h
  ·
    intro g x y x' y' hx' hy'
    apply chi_injective hζ
    rw [chi_bForm, chi_bForm, hx', hy']
    exact adj_genOpH (B) hBhecke hBdia S g x y
  ·
    intro σ c hc hσ x y x' y' hx' hy'
    have hζM : ζ ^ M = 1 := by
      obtain ⟨m, hm⟩ := hpM
      rw [hm, pow_mul, hζ.pow_eq_one, one_pow]
    have hσζ : ∀ n : ℕ, σ (ζ ^ n) = ζ ^ (c * n) := fun n => by
      rw [map_pow σ _ n, hσ _ hζM, ← pow_mul]
    have key : B (x' : JH M H) (y' : JH M H) = σ (B x y) := by
      rw [hx', hy']
      exact hBgal σ c hc hσ x y (nsmul_coe x) (nsmul_coe y)
    apply chi_injective hζ
    rw [chi_bForm, key, smul_eq_mul, chi_natCast_mul hζ, ← hσζ, ← chi_bForm hζ (B) hB1 hBL hBR x y]
    rfl
  ·
    intro A x hx
    exact mem_of_forall_bForm hζ B hB1 hBL hBR hBann A x hx

end S_ModularCurve_exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois
end P2MW
export P2MW.S_ModularCurve_exists_bilinForm_torsion_jH_nondegenerate_genOpH_selfAdjoint_galois (solution)
