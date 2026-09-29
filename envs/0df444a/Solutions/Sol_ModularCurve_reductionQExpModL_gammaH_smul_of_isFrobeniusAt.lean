-- Prove2me | solution 1 for ModularCurve.reductionQExpModL_gammaH_smul_of_isFrobeniusAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0cdf5eb7-432d-5cfe-84ef-dd5d76f8782a

import Mathlib
import Definitions.Def_ModularCurve_QExpReductionModL
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Definitions.Def_ModularCurve_XH
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_Pic0_exists_nsmul_eq
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IsLaurentPlaceReduction laurentIntegralPrincipalDivisors LaurentPrincipalGeneratedByIntegral LaurentReductionInputs laurentReductionDegZero coe_laurentReductionDegZero laurentReduction laurentReduction_mk IsLaurentPlaceReduction.eq_or_const_of_agree ReductionInputsQExpModL reductionQExpModL intSeriesC intSeriesC_zero intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC arithmeticGalois coe_arithmeticGalois_smul galois_smul_pic0_def qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg coeffMap coeffMap_coeff coeffMap_coeffMap coeffMap_id coeffMap_congr coeffMap_algebraMap coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange coeffMap_mem_laurentBaseChange qExpFrobeniusModL coe_qExpFrobeniusModL qExpFrobeniusModL_isIntegral qExpFrobeniusPlaceModL mem_qExpFrobeniusPlaceModL_iff qExpFrobeniusDivPushforwardModL qExpFrobeniusDivPushforwardModL_single QExpFrobeniusInputsModL coe_qExpFrobeniusDegZeroPushforwardModL qExpFrobeniusPushforwardModL qExpFrobeniusPushforwardModL_mk pow_char_eq_coeffMap_frobenius_qExpand translation_mem_GammaH Gamma1_le_GammaH JH qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring JOneES.exists_transcendental_finiteDimensional_laurentBaseChange"
namespace QExpFrobRed
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.ModularCurve HahnSeries IntermediateField"
open scoped Pointwise

section Coeff

variable {R S : Type*} [Field R] [Field S]

theorem coeffMap_intSeriesC (g : R →+* S) (p : PowerSeries ℤ) : coeffMap g (intSeriesC R p) = intSeriesC S p := by
  ext k
  rw [coeffMap_coeff]
  rcases lt_or_ge k 0 with hk | hk
  · rw [intSeriesC, intSeriesC, ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  · lift k to ℕ using hk with k
    rw [intSeriesC, intSeriesC, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map, PowerSeries.coeff_map, eq_intCast, eq_intCast, map_intCast]

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem coeffMap_mem_qExpFunctionFieldC (g : K →+* K) {x : LaurentSeries K} (hx : x ∈ qExpFunctionFieldC K Γ) :
    coeffMap g x ∈ qExpFunctionFieldC K Γ := by
  have hx' : x ∈ (qExpFunctionFieldC K Γ).toSubfield := hx
  rw [qExpFunctionFieldC, adjoin_toSubfield] at hx'
  have key : (Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪ intFormRatiosC K Γ)).map
      (coeffMap g) ≤ (qExpFunctionFieldC K Γ).toSubfield := by
    rw [RingHom.map_field_closure, Subfield.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨k, f, g', pf, pg, hf, hg, hg0, rfl⟩
    · rw [coeffMap_algebraMap]
      exact (qExpFunctionFieldC K Γ).algebraMap_mem _
    · change coeffMap g (intSeriesC K pf / intSeriesC K pg) ∈ qExpFunctionFieldC K Γ
      rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
      exact div_mem_qExpFunctionFieldC f g' hf hg hg0
  exact key ⟨x, hx', rfl⟩

def coeffRingAut (e : K ≃+* K) : (qExpFunctionFieldC K Γ) ≃+* (qExpFunctionFieldC K Γ) where
  toFun x := ⟨coeffMap (e : K →+* K) x, coeffMap_mem_qExpFunctionFieldC K Γ _ x.2⟩
  invFun x := ⟨coeffMap (e.symm : K →+* K) x, coeffMap_mem_qExpFunctionFieldC K Γ _ x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (e.symm : K →+* K) (coeffMap (e : K →+* K) (x : LaurentSeries K)) = x
    rw [coeffMap_coeffMap, coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => e.symm_apply_apply a),
      coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (e : K →+* K) (coeffMap (e.symm : K →+* K) (x : LaurentSeries K)) = x
    rw [coeffMap_coeffMap, coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => e.apply_symm_apply a),
      coeffMap_id]
  map_mul' x y := Subtype.ext (map_mul _ _ _)
  map_add' x y := Subtype.ext (map_add _ _ _)

def coeffSemilinearAut (e : K ≃+* K) : SemilinearAut K (qExpFunctionFieldC K Γ) :=
  ⟨(coeffRingAut K Γ e, e), fun a => Subtype.ext <| by
    show coeffMap (e : K →+* K) (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) (e a)
    exact coeffMap_algebraMap _ a⟩

@[scoped simp] theorem coe_coeffSemilinearAut_smul (e : K ≃+* K) (x : qExpFunctionFieldC K Γ) :
    ((coeffSemilinearAut K Γ e • x : qExpFunctionFieldC K Γ) : LaurentSeries K) = coeffMap (e : K →+* K) x :=
  rfl

theorem coe_toRingAut_coeffSemilinearAut_symm (e : K ≃+* K) (x : qExpFunctionFieldC K Γ) :
    (((SemilinearAut.toRingAut (coeffSemilinearAut K Γ e)).symm x : qExpFunctionFieldC K Γ) : LaurentSeries K) =
      coeffMap (e.symm : K →+* K) x :=
  rfl

omit [Field K] in

theorem coeffMap_qExpand' {R' S' : Type*} [CommRing R'] [CommRing S'] (g : R' →+* S') (n : ℕ) [NeZero n]
    (x : LaurentSeries R') : coeffMap g (qExpand R' n x) = qExpand S' n (coeffMap g x) := by
  ext k
  rw [coeffMap_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

end Coeff

section Frobenius

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ]

def arithFrob : SemilinearAut K (qExpFunctionFieldC K Γ) :=
  coeffSemilinearAut K Γ (frobeniusEquiv K ℓ)

theorem qExpFrobeniusModL_eq_inv_smul_pow (x : qExpFunctionFieldC K Γ) :
    qExpFrobeniusModL K Γ ℓ x = ((arithFrob K Γ ℓ)⁻¹ • x) ^ ℓ := by
  apply Subtype.ext
  rw [coe_qExpFrobeniusModL, SubmonoidClass.coe_pow, arithFrob, SemilinearAut.inv_smul_def,
    coe_toRingAut_coeffSemilinearAut_symm, pow_char_eq_coeffMap_frobenius_qExpand ℓ,
    ← coeffMap_qExpand', coeffMap_coeffMap,
    coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => ?_), coeffMap_id]
  show frobenius K ℓ ((frobeniusEquiv K ℓ).symm a) = a
  exact frobeniusEquiv_symm_apply_frobenius K ℓ a |>.symm ▸ (frobeniusEquiv K ℓ).apply_symm_apply a

theorem qExpFrobeniusPlaceModL_eq_smul (Q : Place K (qExpFunctionFieldC K Γ)) :
    qExpFrobeniusPlaceModL K Γ ℓ Q = arithFrob K Γ ℓ • Q := by
  apply Place.ext
  ext x
  rw [mem_qExpFrobeniusPlaceModL_iff, SemilinearAut.smul_toValuationSubring,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, qExpFrobeniusModL_eq_inv_smul_pow,
    ← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff, Valuation.map_pow,
    pow_le_one_iff (Fact.out : ℓ.Prime).ne_zero]

omit [Fact ℓ.Prime] [CharP K ℓ] [PerfectRing K ℓ] in

theorem deg_restrictAlong_mul_inertiaDegAlong {K' F F' : Type*} [Field K'] [Field F] [Field F']
    [Algebra K' F] [Algebra K' F'] (φ : F →ₐ[K'] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K' F') :
    (w.restrictAlong φ hφ).deg * w.inertiaDegAlong φ hφ = w.deg := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.deg_restrict_mul_inertiaDeg (F := F)

theorem pushforward_single_of_deg_eq_one (Q : Place K (qExpFunctionFieldC K Γ)) (hQ : Q.deg = 1) (n : ℤ) :
    qExpFrobeniusDivPushforwardModL K Γ ℓ (Finsupp.single Q n) = Finsupp.single (arithFrob K Γ ℓ • Q) n := by
  rw [qExpFrobeniusDivPushforwardModL_single, ← qExpFrobeniusPlaceModL_eq_smul]
  have h := deg_restrictAlong_mul_inertiaDegAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) Q
  rw [hQ] at h
  have h1 : Q.inertiaDegAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) = 1 :=
    Nat.eq_one_of_mul_eq_one_left h
  rw [h1, Nat.cast_one, mul_one]

theorem pushforward_eq_mapDomain_of_deg (E : Divisor K (qExpFunctionFieldC K Γ)) (hE : ∀ Q ∈ E.support, Q.deg = 1) :
    qExpFrobeniusDivPushforwardModL K Γ ℓ E = Finsupp.mapDomain (fun Q => arithFrob K Γ ℓ • Q) E := by
  classical
  induction E using Finsupp.induction with
  | zero => simp
  | single_add Q n E hQE hn ih =>
    have hQ : Q.deg = 1 := hE Q (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.notMem_support_iff.mp hQE, add_zero]; exact hn)
    have hE' : ∀ Q' ∈ E.support, Q'.deg = 1 := fun Q' hQ' => hE Q' (by
      rw [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply]
      have hne : Q ≠ Q' := fun h => hQE (h ▸ hQ')
      rw [if_neg hne, zero_add]; exact Finsupp.mem_support_iff.mp hQ')
    rw [map_add, Finsupp.mapDomain_add, ih hE', pushforward_single_of_deg_eq_one K Γ ℓ Q hQ,
      Finsupp.mapDomain_single]

end Frobenius

section Generic

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ]

abbrev FL (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) : Type _ :=
  laurentBaseChange L (qExpFunctionFieldC ℚ Γ)

omit [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ] in

theorem coeffMap_subtype_coeffMap (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (y : LaurentSeries A) :
    coeffMap A.subtype (coeffMap σA y) = coeffMap (σ : L →+* L) (coeffMap A.subtype y) := by
  rw [coeffMap_coeffMap, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext fun a => hσA a) y

theorem mapDomain_frob_agree
    {r : Place L (FL L Γ) → Place k (qExpFunctionFieldC k Γ)}
    (hr : IsLaurentPlaceReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) r)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = frobenius k ℓ (π a))
    {D : Divisor L (FL L Γ)}
    (hD : D ∈ laurentIntegralPrincipalDivisors A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ)) :
    Finsupp.mapDomain ((fun Q => arithFrob k Γ ℓ • Q) ∘ r) D =
      Finsupp.mapDomain (r ∘ fun P => arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ • P) D := by
  obtain ⟨y, hy, hyk, hne, hDy⟩ := hD
  set g := arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ with hg
  set φ := arithFrob k Γ ℓ with hφ
  set y' : LaurentSeries A := coeffMap σA y with hy'def
  have himg : coeffMap A.subtype y' = coeffMap (σ : L →+* L) (coeffMap A.subtype y) :=
    coeffMap_subtype_coeffMap σ σA hσA y
  have hy' : coeffMap A.subtype y' ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) := by
    rw [himg]; exact coeffMap_mem_laurentBaseChange σ hy
  have hred : coeffMap π y' = coeffMap (frobenius k ℓ) (coeffMap π y) := by
    rw [hy'def, coeffMap_coeffMap, coeffMap_coeffMap]
    exact coeffMap_congr (RingHom.ext fun a => hπ a) y

  have hredφ : coeffMap π y' =
      ((φ • (⟨coeffMap π y, hyk⟩ : qExpFunctionFieldC k Γ) : qExpFunctionFieldC k Γ) : LaurentSeries k) := by
    rw [hred, hφ, arithFrob, coe_coeffSemilinearAut_smul]
    exact coeffMap_congr (RingHom.ext fun a => rfl) _
  have hyk' : coeffMap π y' ∈ qExpFunctionFieldC k Γ :=
    hredφ ▸ (φ • (⟨coeffMap π y, hyk⟩ : qExpFunctionFieldC k Γ)).2
  have hne' : coeffMap π y' ≠ 0 := by
    rw [hred]; intro h0; apply hne
    have := congrArg (coeffMap ((frobeniusEquiv k ℓ).symm : k →+* k)) h0
    rw [map_zero, coeffMap_coeffMap, coeffMap_congr (g := RingHom.id k) (RingHom.ext fun a => ?_),
      coeffMap_id] at this
    · exact this
    · exact frobeniusEquiv_symm_apply_frobenius k ℓ a
  have hyeq : (⟨coeffMap π y', hyk'⟩ : qExpFunctionFieldC k Γ) = φ • ⟨coeffMap π y, hyk⟩ :=
    Subtype.ext hredφ

  have hgx : g • (⟨coeffMap A.subtype y, hy⟩ : FL L Γ) = ⟨coeffMap A.subtype y', hy'⟩ :=
    Subtype.ext (by rw [coe_arithmeticGalois_smul]; exact himg.symm)

  have hD' : ∀ P, (g • D) P = P.ord (⟨coeffMap A.subtype y', hy'⟩ : FL L Γ) := by
    intro P
    rw [SemilinearAut.divisor_smul_apply, hDy, ← hgx, ← SemilinearAut.ord_smul g (g⁻¹ • P), smul_inv_smul]

  rw [Finsupp.mapDomain_comp, Finsupp.mapDomain_comp, ← SemilinearAut.divisor_smul_def,
    ← SemilinearAut.divisor_smul_def]
  ext Q
  rw [SemilinearAut.divisor_smul_apply, hr.2 y hy hyk hne D hDy (φ⁻¹ • Q),
    hr.2 y' hy' hyk' hne' (g • D) hD' Q, hyeq, ← SemilinearAut.ord_smul φ (φ⁻¹ • Q), smul_inv_smul]

omit [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ] in

theorem degree_eq_zero_of_mem_principal {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) : Divisor.degree D = 0 := by
  obtain ⟨f, hf, hDf⟩ := hD
  obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : D = D' := Finsupp.ext fun v => by rw [hDf v, hD' v]
  rw [this, hdeg]

omit [Fact ℓ.Prime] [CharP k ℓ] [PerfectRing k ℓ] in

theorem mapDomain_eq_zero_of_const {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F']
    [Algebra K' F'] {r : Place K F → Place K' F'} (hconst : ∀ P Q, r P = r Q) (hdeg : ∀ P : Place K F, P.deg = 1)
    {D : Divisor K F} (hD : D ∈ Divisor.degZero (K := K) (F := F)) : Finsupp.mapDomain r D = 0 := by
  rcases isEmpty_or_nonempty (Place K F) with hE | ⟨⟨P₀⟩⟩
  · have : D = 0 := Finsupp.ext fun P => isEmptyElim P
    rw [this, Finsupp.mapDomain_zero]
  · have hmapconst : ∀ D : Divisor K F, Finsupp.mapDomain r D = Finsupp.single (r P₀) (Divisor.degree D) := by
      intro D
      induction D using Finsupp.induction with
      | zero => simp
      | single_add P n D _ _ ih =>
        rw [Finsupp.mapDomain_add, ih, Finsupp.mapDomain_single, hconst P P₀, map_add,
          Divisor.degree_single, hdeg, Nat.cast_one, mul_one, ← Finsupp.single_add, add_comm]
    rw [hmapconst D, (Divisor.mem_degZero.mp hD), Finsupp.single_zero]

set_option maxHeartbeats 3200000 in

theorem laurentReduction_smul_eq_qExpFrobeniusPushforward
    [HasPrincipalDivisors L (FL L Γ)] [HasPrincipalDivisors k (qExpFunctionFieldC k Γ)]
    (hfin : FiniteAlong k (qExpFrobeniusModL k Γ ℓ))
    (hFI : FundamentalIdentityAlong k (qExpFrobeniusModL k Γ ℓ) (qExpFrobeniusModL_isIntegral k Γ ℓ))
    (hN : NormFormulaAlong k (qExpFrobeniusModL k Γ ℓ) hfin)
    (h : LaurentReductionInputs A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ))
    (hdegL : ∀ P : Place L (FL L Γ), P.deg = 1)
    (hdegk : ∀ Q : Place k (qExpFunctionFieldC k Γ), Q.deg = 1)
    (hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 L (FL L Γ), ∃ y : Pic0 L (FL L Γ), n • y = x)
    (σ : L ≃ₐ[ℚ] L) (σA : A →+* A) (hσA : ∀ a : A, (σA a : L) = σ a)
    (hπ : ∀ a, π (σA a) = frobenius k ℓ (π a))
    (x : Pic0 L (FL L Γ)) :
    laurentReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) (σ • x) =
      qExpFrobeniusPushforwardModL k Γ ℓ (laurentReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) x) := by
  set r := h.choose with hrdef
  have hr : IsLaurentPlaceReduction A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) r := h.choose_spec.1
  have hgen : LaurentPrincipalGeneratedByIntegral A π (qExpFunctionFieldC ℚ Γ) (qExpFunctionFieldC k Γ) :=
    h.choose_spec.2
  set g := arithmeticGalois (qExpFunctionFieldC ℚ Γ) σ with hg
  set φ := arithFrob k Γ ℓ with hφ
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk, laurentReduction_mk h, laurentReduction_mk h,
    qExpFrobeniusPushforwardModL_mk hfin hFI hN]

  rcases IsLaurentPlaceReduction.eq_or_const_of_agree (r₁ := (fun Q => φ • Q) ∘ r)
      (r₂ := r ∘ fun P => g • P) hgen (fun D hD => mapDomain_frob_agree ℓ hr σ σA hσA hπ hD) hdegL hdiv with
    key | hconst
  · congr 1
    apply Subtype.ext
    rw [coe_laurentReductionDegZero, coe_qExpFrobeniusDegZeroPushforwardModL, coe_laurentReductionDegZero,
      SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_def, ← Finsupp.mapDomain_comp, ← hg,
      show h.choose = r from rfl, ← key, Finsupp.mapDomain_comp]
    refine (pushforward_eq_mapDomain_of_deg k Γ ℓ _ fun Q hQ => ?_).symm
    exact hdegk Q
  ·
    have hconst' : ∀ P Q, r P = r Q := fun P Q => smul_left_cancel φ (hconst P Q)
    have h0 : ∀ E : Divisor.degZero (K := L) (F := FL L Γ),
        laurentReductionDegZero h.choose h.choose_spec.1.1 E = 0 := fun E =>
      Subtype.ext (by rw [coe_laurentReductionDegZero]; exact mapDomain_eq_zero_of_const hconst' hdegL E.2)
    rw [h0, h0, map_zero]

end Generic

section Modular

open ValuationSubring

variable {K : Type*} [Field K]

omit [Field K] in

theorem intSeriesC_injective (K : Type*) [Field K] [CharZero K] : Function.Injective (intSeriesC K) :=
  fun p q h => PowerSeries.map_injective (Int.castRingHom K) Int.cast_injective
    (HahnSeries.ofPowerSeries_injective h)

theorem mem_range_of_isAlgebraic [IsAlgClosed K] {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    {x : qExpFunctionFieldC K Γ} (hx : IsAlgebraic K x) :
    (x : LaurentSeries K) ∈ Set.range (algebraMap K (LaurentSeries K)) := by
  have hint : IsIntegral K x := hx.isIntegral
  have hdeg : (minpoly K x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ : x ∈ (algebraMap K (qExpFunctionFieldC K Γ)).range := minpoly.mem_range_of_degree_eq_one K x hdeg
  exact ⟨c, by rw [← hc]; rfl⟩

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem main (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    {ℓ : ℕ} [Fact ℓ.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ModularCurve.ReductionInputsQExpModL A Γ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ)) :
    ModularCurve.reductionQExpModL A Γ (σ • z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A) Γ ℓ
        (ModularCurve.reductionQExpModL A Γ z) := by

  haveI : IsAlgClosed (IsLocalRing.ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  haveI : PerfectField (IsLocalRing.ResidueField A) := IsAlgClosed.perfectField _
  haveI : ExpChar (IsLocalRing.ResidueField A) ℓ := ExpChar.prime (Fact.out : ℓ.Prime)
  haveI : PerfectRing (IsLocalRing.ResidueField A) ℓ := PerfectField.toPerfectRing ℓ

  obtain ⟨t, ht, hfd⟩ := ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
    (AlgebraicClosure ℚ) Γ hT
  haveI : IsCurveOver (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht hfd
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ) := IsCurveOver.hasPrincipalDivisors
  have hdegL : ∀ P : Place (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ), P.deg = 1 :=
    IsCurveOver.deg_eq_one_of_isAlgClosed
  have hdiv : ∀ n : ℕ, n ≠ 0 → ∀ x : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ),
      ∃ y : Pic0 (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ), n • y = x :=
    fun n hn x => AlgebraicCurve.Pic0.exists_nsmul_eq (AlgebraicClosure ℚ) (FL (AlgebraicClosure ℚ) Γ)
      ⟨t, ht, hfd⟩ n hn x

  obtain ⟨hσmem, hσfrob⟩ := hσ
  let d : A.decompositionSubgroup ℚ := ⟨σ, hσmem⟩
  let σA : A →+* A := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  have hσA : ∀ a : A, (σA a : AlgebraicClosure ℚ) = σ a := fun a => rfl
  have hπ : ∀ a : A, IsLocalRing.residue A (σA a) = frobenius _ ℓ (IsLocalRing.residue A a) := by
    intro a
    show IsLocalRing.residue A (d • a) = _
    rw [IsLocalRing.ResidueField.residue_smul, frobenius_def]
    exact hσfrob _

  by_cases hS : intFormRatiosC (IsLocalRing.ResidueField A) Γ ⊆
      Set.range (algebraMap (IsLocalRing.ResidueField A) (LaurentSeries (IsLocalRing.ResidueField A)))
  ·
    have hle : qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ ≤ ⊥ := by
      rw [qExpFunctionFieldC, adjoin_le_iff]
      intro s hs
      exact IntermediateField.mem_bot.mpr (hS hs)
    haveI : IsEmpty (Place (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)) := by
      refine ⟨fun v => v.ne_top' ?_⟩
      ext y
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp (hle y.2)
      have : y = algebraMap (IsLocalRing.ResidueField A) _ c := Subtype.ext hc.symm
      rw [this]
      exact v.algebraMap_mem' c
    haveI : Subsingleton (Pic0 (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨Da, rfl⟩ := Pic0.mk_surjective a
      obtain ⟨Db, rfl⟩ := Pic0.mk_surjective b
      congr 1
      exact Subtype.ext (Finsupp.ext fun P => isEmptyElim P)
    exact Subsingleton.elim _ _
  ·
    obtain ⟨s, hs, hsc⟩ := Set.not_subset.mp hS
    obtain ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hs
    set xbar : qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ :=
      ⟨intSeriesC _ pf / intSeriesC _ pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩ with hxbar
    have htr : Transcendental (IsLocalRing.ResidueField A) xbar := fun halg => hsc (mem_range_of_isAlgebraic halg)

    have hpg : pg ≠ 0 := fun h0 => hg0 (by rw [h0, intSeriesC_zero])
    have hg0ℚ : intSeriesC ℚ pg ≠ 0 := fun h0 => hpg (intSeriesC_injective ℚ (h0.trans (intSeriesC_zero ℚ).symm))
    set X : FL (AlgebraicClosure ℚ) Γ :=
      ⟨coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg),
        coeffEmb_mem_laurentBaseChange _ (div_mem_qExpFunctionFieldC f g hf hg hg0ℚ)⟩ with hXdef
    have hX : (X : LaurentSeries (AlgebraicClosure ℚ)) =
        intSeriesC (AlgebraicClosure ℚ) pf / intSeriesC (AlgebraicClosure ℚ) pg := by
      show coeffEmb (AlgebraicClosure ℚ) (intSeriesC ℚ pf / intSeriesC ℚ pg) = _
      rw [map_div₀, coeffEmb, coeffMap_intSeriesC, coeffMap_intSeriesC]

    obtain ⟨hfdk, -⟩ := ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring A
      (IsLocalRing.residue A) Γ ⟨t, ht, hfd⟩ pf pg X hX xbar rfl htr

    obtain ⟨hP, hfin, hFI, hN⟩ := ((ModularCurve.qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
      (IsLocalRing.ResidueField A) Γ ⟨xbar, htr, hfdk⟩).1 :
        QExpFrobeniusInputsModL (IsLocalRing.ResidueField A) Γ ℓ)
    haveI := hP
    haveI : IsCurveOver (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :=
      AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField htr hfdk
    have hdegk : ∀ Q : Place (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ),
        Q.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
    exact laurentReduction_smul_eq_qExpFrobeniusPushforward ℓ hfin hFI hN h hdegL hdegk hdiv σ σA hσA hπ z

end Modular

end ModularCurve.QExpFrobRed
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.ModularCurve.QExpFrobRed"
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.ModularCurve P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt.ModularCurve.QExpFrobRed"

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (IsLocalRing.ResidueField A) ℓ]
    (h : ModularCurve.ReductionInputsQExpModL A (CohCarrier.GammaH M H))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : A.IsFrobeniusAt σ ℓ)
    (z : ModularCurve.JH M H) :
    ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) (σ • z) =
      ModularCurve.qExpFrobeniusPushforwardModL (IsLocalRing.ResidueField A)
        (CohCarrier.GammaH M H) ℓ
        (ModularCurve.reductionQExpModL A (CohCarrier.GammaH M H) z) :=
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  ModularCurve.QExpFrobRed.main (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) A h σ hσ z

end S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt
end P2MW
export P2MW.S_ModularCurve_reductionQExpModL_gammaH_smul_of_isFrobeniusAt (solution)
