-- Prove2me | solution 1 for ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/e360738b-6cb5-5cb6-8e28-2ae905a9f568

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace
import Theorems.Thm_ModularCurve_exists_mem_riemannRochSpace_mul_eq_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_ne_zero
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none"

set_option autoImplicit false
set_option Elab.async false

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem solution
    (N : ℕ) [NeZero N] {ι : Type} [Fintype ι] (t : ι → modularFunctionFieldBar N) (ht0 : ∀ l, t l ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ (Fbar : Type) [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar),
      (∀ f : modularFunctionFieldBar N,
        (∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) →
        (∃ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits) →
        ∃ h : f ∈ C.integers, C.residue ⟨f, h⟩ ≠ 0) →
    ∀ l : ι, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
      (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
      ∃ h : c • t l ∈ C.integers, C.residue ⟨c • t l, h⟩ ≠ 0 := by
  classical

  have hq : ∀ l, ∃ n : ℕ, ∃ u g : modularFunctionFieldBar N,
      u ≠ 0 ∧ u ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) ∧
      g ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) ∧ t l * u = g :=
    fun l => ModularCurve.exists_mem_riemannRochSpace_mul_eq_of_ne_zero N (t l) (ht0 l)
  choose nf u g hu0 hu hg htu using hq
  have hg0 : ∀ l, g l ≠ 0 := fun l => by rw [← htu l]; exact mul_ne_zero (ht0 l) (hu0 l)

  set n : ℕ := Finset.univ.sup nf with hn
  have hmono : ∀ (l : ι) (x : modularFunctionFieldBar N),
      x ∈ riemannRochSpace ((nf l : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) →
      x ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) := by
    intro l x hx
    have hle : nf l ≤ n := Finset.le_sup (Finset.mem_univ l)
    rw [mem_riemannRochSpace_iff] at hx ⊢
    intro v
    rcases hx v with h | h
    · exact Or.inl h
    · right
      rw [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul] at h ⊢
      split_ifs at h ⊢ with hv
      · omega
      · simpa using h

  set s : ι ⊕ ι → modularFunctionFieldBar N := Sum.elim g u with hs
  have hsV : ∀ j, s j ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) := by
    rintro (l | l)
    · exact hmono l _ (hg l)
    · exact hmono l _ (hu l)
  have hs0 : ∀ j, s j ≠ 0 := by
    rintro (l | l)
    · exact hg0 l
    · exact hu0 l
  obtain ⟨B₀, hB₀⟩ :=
    ModularCurve.exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_mem_riemannRochSpace
      N n s hsV hs0 p hp
  refine ⟨B₀ + B₀, fun A hA Fbar _ _ C hcrit l => ?_⟩
  have hcrit' : ∀ f : modularFunctionFieldBar N,
      f ∈ riemannRochSpace ((n : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)) →
      (∀ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) →
      (∃ k : ℤ, (f : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∉ A.nonunits) →
      ∃ h : f ∈ C.integers, C.residue ⟨f, h⟩ ≠ 0 := fun f _ hf hu' => hcrit f hf hu'
  obtain ⟨cg, hcg0, hcg1, hcg2, hgint, hgres⟩ := hB₀ A hA Fbar C hcrit' (Sum.inl l)
  obtain ⟨cu, hcu0, hcu1, hcu2, huint, hures⟩ := hB₀ A hA Fbar C hcrit' (Sum.inr l)
  simp only [hs, Sum.elim_inl, Sum.elim_inr] at hgint hgres huint hures

  have hunit : IsUnit (⟨cu • u l, huint⟩ : C.integers) := by
    by_contra h
    apply hures
    have hmem : (⟨cu • u l, huint⟩ : C.integers) ∈ IsLocalRing.maximalIdeal C.integers :=
      (IsLocalRing.mem_maximalIdeal _).mpr h
    rw [← C.ker_residue] at hmem
    exact hmem
  obtain ⟨w, hw⟩ := hunit
  have hwinv_val : ((w⁻¹ : C.integersˣ) : C.integers).1 = (cu • u l)⁻¹ := by
    have h1 : ((w : C.integers) : modularFunctionFieldBar N) * ((w⁻¹ : C.integersˣ) : C.integers) = 1 := by
      have h := congrArg Subtype.val w.mul_inv
      rwa [MulMemClass.coe_mul, OneMemClass.coe_one] at h
    rw [hw] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hinv_mem : (cu • u l)⁻¹ ∈ C.integers := by
    rw [← hwinv_val]; exact ((w⁻¹ : C.integersˣ) : C.integers).2
  have hinv_res : C.residue ⟨(cu • u l)⁻¹, hinv_mem⟩ ≠ 0 := by
    have : (⟨(cu • u l)⁻¹, hinv_mem⟩ : C.integers) = ((w⁻¹ : C.integersˣ) : C.integers) := Subtype.ext hwinv_val.symm
    rw [this]
    exact (C.residue.isUnit_map (w⁻¹).isUnit).ne_zero

  have htl : t l = g l * (u l)⁻¹ := by rw [← htu l, mul_assoc, mul_inv_cancel₀ (hu0 l), mul_one]
  have hct : (cg * cu⁻¹) • t l = (cg • g l) * (cu • u l)⁻¹ := by
    rw [htl, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, map_inv₀, mul_inv]
    ring
  refine ⟨cg * cu⁻¹, mul_ne_zero hcg0 (inv_ne_zero hcu0), ?_, ?_, ?_⟩
  · have : (p : AlgebraicClosure ℚ) ^ (B₀ + B₀) * (cg * cu⁻¹)
        = ((p : AlgebraicClosure ℚ) ^ B₀ * cg) * ((p : AlgebraicClosure ℚ) ^ B₀ * cu⁻¹) := by rw [pow_add]; ring
    rw [this]; exact mul_mem hcg1 hcu2
  · have : (p : AlgebraicClosure ℚ) ^ (B₀ + B₀) * (cg * cu⁻¹)⁻¹
        = ((p : AlgebraicClosure ℚ) ^ B₀ * cg⁻¹) * ((p : AlgebraicClosure ℚ) ^ B₀ * cu) := by
      rw [pow_add, mul_inv, inv_inv]; ring
    rw [this]
    exact mul_mem hcg2 hcu1
  · have hmem : (cg * cu⁻¹) • t l ∈ C.integers := by
      rw [hct]
      exact mul_mem hgint hinv_mem
    refine ⟨hmem, ?_⟩
    have hprod : (⟨(cg * cu⁻¹) • t l, hmem⟩ : C.integers)
        = ⟨cg • g l, hgint⟩ * ⟨(cu • u l)⁻¹, hinv_mem⟩ := Subtype.ext hct
    rw [hprod, map_mul]
    exact mul_ne_zero hgres hinv_res

end S_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_ne_zero
end P2MW
export P2MW.S_ModularCurve_exists_uniform_window_smul_mem_integers_of_qCoeff_criterion_of_ne_zero (solution)
