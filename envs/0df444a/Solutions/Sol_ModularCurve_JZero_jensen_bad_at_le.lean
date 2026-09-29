-- Prove2me | solution 1 for ModularCurve.JZero.jensen_bad_at_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ea52c142-308b-50c8-994c-0a8c08f86c2a

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Theorems.Thm_NumberField_exists_isNonarchimedean_absoluteValue_extends
import Theorems.Thm_ModularCurve_exists_ord_add_embDivisor_eq_zero
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_add
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_mul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_smul
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_forall_lt_taylorCoeff_eq_zero_iff_le_ord
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_taylorCoeff_ord_ne_zero
import Theorems.Thm_PowerSeries_norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero
import Theorems.Thm_PowerSeries_norm_coeff_sum_C_mul_prod_mul_pow_le
import Theorems.Thm_PowerSeries_taylorShift_sum_C_mul_prod
import Theorems.Thm_AbsoluteValue_Completion_isUltrametricDist_of_isNonarchimedean
import Theorems.Thm_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm
import Theorems.Thm_ModularCurve_JZero_exists_chart_of_isPivot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_bad_at_le
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.jqNModC_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve KaehlerDifferential

noncomputable section

namespace P2MW

section Eval

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero (Q : Place K F) : Q.evalAt (0 : F) = 0 := by
  have h := Q.evalAt_algebraMap_eq (0 : K)
  rwa [map_zero] at h

theorem ord_nonneg_of_mem (Q : Place K F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ Q.toValuationSubring) :
    0 ≤ Q.ord f := by
  have h1 : Q.adicValuation f ≤ 1 := by
    have := Q.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : Q.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := Q.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (Q.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (Q.adicValuation f))
  omega

theorem mem_of_eq_zero_or_ord_nonneg (Q : Place K F) {f : F} (h : f = 0 ∨ 0 ≤ Q.ord f) :
    f ∈ Q.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · exact Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 (h.resolve_left hf0)

theorem ord_eq_zero_of_evalAt_ne_zero (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f ≠ 0) : Q.ord f = 0 := by
  have hres : IsLocalRing.residue Q.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply Q.algebraMap_residueField_injective
    rw [Q.algebraMap_evalAt hQ hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := Q.ord_coe_unit u
  rwa [hu] at this

theorem ne_zero_of_evalAt_ne_zero (Q : Place K F) {f : F} (h : Q.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl; exact h (evalAt_zero Q)

theorem evalAt_eq_zero_of_ord_pos (Q : Place K F) (hQ : Q.IsRational) {f : F}
    (hf : f ∈ Q.toValuationSubring) (h : 0 < Q.ord f) : Q.evalAt f = 0 := by
  by_contra hne
  have := ord_eq_zero_of_evalAt_ne_zero Q hQ hf hne
  omega

theorem ord_pos_of_evalAt_eq_zero (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ Q.toValuationSubring) (h : Q.evalAt f = 0) : 0 < Q.ord f := by
  rcases (ord_nonneg_of_mem Q hf0 hf).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd h (Q.evalAt_ne_zero_of_ord_eq_zero hQ hf0 heq.symm)

theorem evalAt_add_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f + g) = Q.evalAt f + Q.evalAt g := by
  apply Q.algebraMap_residueField_injective
  rw [map_add, Q.algebraMap_evalAt hQ (add_mem hf hg), Q.algebraMap_evalAt hQ hf, Q.algebraMap_evalAt hQ hg,
    ← map_add]
  rfl

theorem evalAt_neg_of_mem (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf : f ∈ Q.toValuationSubring) :
    Q.evalAt (-f) = -Q.evalAt f := by
  apply Q.algebraMap_residueField_injective
  rw [map_neg, Q.algebraMap_evalAt hQ (neg_mem hf), Q.algebraMap_evalAt hQ hf, ← map_neg]
  rfl

theorem evalAt_sub_of_mem (Q : Place K F) (hQ : Q.IsRational) {f g : F}
    (hf : f ∈ Q.toValuationSubring) (hg : g ∈ Q.toValuationSubring) :
    Q.evalAt (f - g) = Q.evalAt f - Q.evalAt g := by
  rw [sub_eq_add_neg, evalAt_add_of_mem Q hQ hf (neg_mem hg), evalAt_neg_of_mem Q hQ hg, ← sub_eq_add_neg]

theorem smul_mem_of_mem (Q : Place K F) (a : K) {f : F} (hf : f ∈ Q.toValuationSubring) :
    a • f ∈ Q.toValuationSubring := by
  rw [Algebra.smul_def]; exact mul_mem (Q.algebraMap_mem' a) hf

theorem evalAt_smul_of_mem (Q : Place K F) (hQ : Q.IsRational) (a : K) {f : F}
    (hf : f ∈ Q.toValuationSubring) : Q.evalAt (a • f) = a * Q.evalAt f := by
  rw [Algebra.smul_def, Q.evalAt_mul_of_mem hQ (Q.algebraMap_mem' a) hf, Q.evalAt_algebraMap_eq]

theorem evalAt_sum_smul_of_mem {ι : Type*} (S : Finset ι) (Q : Place K F) (hQ : Q.IsRational)
    (c : ι → K) {f : ι → F} (hf : ∀ i, f i ∈ Q.toValuationSubring) :
    Q.evalAt (∑ i ∈ S, c i • f i) = ∑ i ∈ S, c i * Q.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact evalAt_zero Q
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      evalAt_add_of_mem Q hQ (smul_mem_of_mem Q _ (hf a)) (sum_mem fun i _ => smul_mem_of_mem Q _ (hf i)),
      evalAt_smul_of_mem Q hQ _ (hf a), ih]

theorem inv_mem_of_ord_eq_zero (Q : Place K F) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    f⁻¹ ∈ Q.toValuationSubring :=
  Q.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf0) (by rw [Q.ord_inv, h, neg_zero])

theorem evalAt_mul_evalAt_inv (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) :
    Q.evalAt f * Q.evalAt f⁻¹ = 1 := by
  rw [← Q.evalAt_mul_of_mem hQ (Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.ge) (inv_mem_of_ord_eq_zero Q hf0 h),
    mul_inv_cancel₀ hf0, Q.evalAt_one]

theorem exists_ord_eq_one (Q : Place K F) : ∃ t : F, Q.ord t = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  exact ⟨(π : F), Q.ord_coe_irreducible hπ⟩

end Eval

end P2MW

end

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve ModularCurve

noncomputable section

namespace P2MJB

section Prox

theorem abv_sub_le_max {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (a b : K) : μ (a - b) ≤ max (μ a) (μ b) := by
  have h := hμ a (-b)
  rw [← sub_eq_add_neg, μ.map_neg] at h
  exact h

theorem prox_eq_zero_of_coord_eq_zero {K : Type*} [Field K] {r : ℕ} (μ : AbsoluteValue K ℝ)
    (hμ : IsNonarchimedean μ) (x y : Fin r → K) (i : Fin r) (hyi : y i = 0)
    (hxi : ∀ j, μ (x j) ≤ μ (x i)) (hx0 : 0 < μ (x i))
    (b : Fin r) (hyb : ∀ j, μ (y j) ≤ μ (y b)) (hy0 : 0 < μ (y b)) : prox μ x y = 0 := by
  haveI : Nonempty (Fin r) := ⟨i⟩
  have hX : (⨆ j, μ (x j)) = μ (x i) :=
    le_antisymm (ciSup_le hxi) (le_ciSup (f := fun j => μ (x j)) (Set.finite_range _).bddAbove i)
  have hY : (⨆ j, μ (y j)) = μ (y b) :=
    le_antisymm (ciSup_le hyb) (le_ciSup (f := fun j => μ (y j)) (Set.finite_range _).bddAbove b)
  have hW : (⨆ q : Fin r × Fin r, μ (x q.1 * y q.2 - x q.2 * y q.1)) = μ (x i) * μ (y b) := by
    refine le_antisymm (ciSup_le fun q => ?_) ?_
    · refine (abv_sub_le_max μ hμ _ _).trans (max_le ?_ ?_)
      · rw [map_mul]
        exact mul_le_mul (hxi q.1) (hyb q.2) (apply_nonneg _ _) hx0.le
      · rw [map_mul]
        exact mul_le_mul (hxi q.2) (hyb q.1) (apply_nonneg _ _) hx0.le
    · have h := le_ciSup (f := fun q : Fin r × Fin r => μ (x q.1 * y q.2 - x q.2 * y q.1))
        (Set.finite_range _).bddAbove (i, b)
      have hib : μ (x i * y b - x b * y i) = μ (x i) * μ (y b) := by
        rw [hyi, mul_zero, sub_zero, map_mul]
      rw [hib] at h
      exact h
  unfold prox
  rw [hX, hY, hW, Real.log_mul hx0.ne' hy0.ne']
  ring

theorem prox_coe {r : ℕ} {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [NumberField ↥L]
    (ν : NumberField.FinitePlace ↥L) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (hμν : ∀ a : ↥L, μ (a : AlgebraicClosure ℚ) = ν a)
    (x y : Fin r → ↥L) (X Y : Fin r → AlgebraicClosure ℚ)
    (hx : ∀ i, ((x i : ↥L) : AlgebraicClosure ℚ) = X i) (hy : ∀ i, ((y i : ↥L) : AlgebraicClosure ℚ) = Y i) :
    prox ν x y = prox μ X Y := by
  have h1 : ∀ i, ν (x i) = μ (X i) := fun i => by rw [← hμν, hx]
  have h2 : ∀ i, ν (y i) = μ (Y i) := fun i => by rw [← hμν, hy]
  have h3 : ∀ q : Fin r × Fin r, ν (x q.1 * y q.2 - x q.2 * y q.1) = μ (X q.1 * Y q.2 - X q.2 * Y q.1) := by
    intro q
    rw [← hμν]
    push_cast
    rw [hx, hx, hy, hy]
  unfold prox
  simp only [h1, h2, h3]

end Prox

section Bar

variable (N : ℕ) [NeZero N]

theorem isRational_bar (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

variable {N}

theorem exists_forall_ord_le {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem evalVec_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]; simp only [dif_pos hr]

theorem secVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (k : ℕ) (u : modularFunctionFieldBar N) :
    secVal s v k u = v.evalAt (u * ((s (pivotIndex s v hr))⁻¹) ^ k) := by
  rw [secVal]; simp only [dif_pos hr]

theorem regVal_apply {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N)
    (o : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (t : modularFunctionFieldBar N) (k e : ℕ)
    (u : modularFunctionFieldBar N) :
    regVal s o t k e u = o.evalAt (u * ((s (pivotIndex s o hr))⁻¹) ^ k * (t⁻¹) ^ e) := by
  rw [regVal]; simp only [dif_pos hr]

theorem effective_of_mem {k : ℕ} {u : modularFunctionFieldBar N} (hu0 : u ≠ 0)
    (hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    ∀ w, 0 ≤ B w := by
  intro w
  rw [hB w]
  have := ((mem_riemannRochSpace_iff.mp hu) w).resolve_left hu0
  linarith

theorem degree_eq_sum_bar (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (D.degree : ℝ) = D.sum (fun _ n => (n : ℝ)) := by
  classical
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun w _ => ?_
  simp [deg_eq_one_modularFunctionFieldBar N w]

theorem mass_eq {k : ℕ} {u : modularFunctionFieldBar N} (hu0 : u ≠ 0)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (Du : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hDu : ∀ w, Du w = w.ord u) (hDudeg : Du.degree = 0) :
    B.sum (fun _ n => (n : ℝ)) = (k : ℝ) * embDegree N := by
  have hBeq : B = Du + (k : ℤ) • embDivisor N := by
    ext w; rw [hB w, Finsupp.add_apply, hDu w]
  rw [← degree_eq_sum_bar, hBeq, map_add, map_zsmul, hDudeg, zero_add, embDivisor, map_zsmul, Divisor.degree_single,
    deg_eq_one_modularFunctionFieldBar N]
  simp only [smul_eq_mul, zsmul_eq_mul]
  push_cast; ring

end Bar

end P2MJB

end

namespace P2MJB

open AlgebraicCurve ModularCurve

theorem apply_le_mass {N : ℕ} [NeZero N] (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hB : ∀ w, 0 ≤ B w) (P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    (B P : ℝ) ≤ B.sum (fun _ n => (n : ℝ)) := by
  classical
  have h := Finsupp.add_sum_erase' B P (fun _ n => (n : ℝ)) (fun w => by simp)
  have hnn : 0 ≤ (B.erase P).sum (fun _ n => (n : ℝ)) := by
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun w _ => ?_
    by_cases hw : w = P
    · rw [hw, Finsupp.erase_same]; simp
    · rw [Finsupp.erase_ne hw]; exact_mod_cast hB w
  linarith

section Monomial

variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem mul_mem_rr_add' {D₁ D₂ : Divisor (AlgebraicClosure ℚ) F} {f g : F} (hf : f ∈ riemannRochSpace D₁)
    (hg : g ∈ riemannRochSpace D₂) : f * g ∈ riemannRochSpace (D₁ + D₂) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

theorem one_mem_rr_zero' : (1 : F) ∈ riemannRochSpace (0 : Divisor (AlgebraicClosure ℚ) F) := by
  rw [mem_riemannRochSpace_iff]
  intro w; right; rw [Place.ord_one, Finsupp.zero_apply, neg_zero]

theorem prod_mem_rr' (E : Divisor (AlgebraicClosure ℚ) F) {r : ℕ} (s : Fin r → F)
    (hsE : ∀ i, s i ∈ riemannRochSpace E) :
    ∀ (k : ℕ) (φ : Fin k → Fin r), (∏ l, s (φ l)) ∈ riemannRochSpace ((k : ℤ) • E) := by
  intro k
  induction k with
  | zero =>
    intro φ
    rw [Finset.univ_eq_empty, Finset.prod_empty, Nat.cast_zero, zero_smul]
    exact one_mem_rr_zero'
  | succ k ih =>
    intro φ
    rw [Fin.prod_univ_succ]
    have h : ((k + 1 : ℕ) : ℤ) • E = E + (k : ℤ) • E := by push_cast; rw [add_smul, one_smul, add_comm]
    rw [h]
    exact mul_mem_rr_add' (hsE _) (ih fun l => φ l.succ)

theorem mem_rr_of_monomialRep' (E : Divisor (AlgebraicClosure ℚ) F) {r : ℕ} (s : Fin r → F)
    (hsE : ∀ i, s i ∈ riemannRochSpace E) {k : ℕ} (cf : (Fin k → Fin r) → AlgebraicClosure ℚ) (u : F)
    (hu : u = ∑ φ : Fin k → Fin r, cf φ • ∏ l, s (φ l)) : u ∈ riemannRochSpace ((k : ℤ) • E) := by
  rw [hu]
  exact Submodule.sum_mem _ fun φ _ => Submodule.smul_mem _ _ (prod_mem_rr' E s hsE k φ)

end Monomial

theorem sum_le_sum_of_le' {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]
    (D D' : Divisor (AlgebraicClosure ℚ) F) (hD'0 : ∀ w, 0 ≤ D' w) (hle : ∀ w, D' w ≤ D w)
    (P : Place (AlgebraicClosure ℚ) F → ℝ) (hP : ∀ w, 0 ≤ P w) :
    (D'.sum fun w n => (n : ℝ) * P w) ≤ D.sum fun w n => (n : ℝ) * P w := by
  classical
  have hsplit : (D.sum fun w n => (n : ℝ) * P w) = (D'.sum fun w n => (n : ℝ) * P w) + ((D - D').sum fun w n => (n : ℝ) * P w) := by
    have : D = D' + (D - D') := by abel
    conv_lhs => rw [this]
    rw [Finsupp.sum_add_index' (fun w => by simp) (fun w a b => by push_cast; ring)]
  rw [hsplit]
  have hnn : 0 ≤ (D - D').sum fun w n => (n : ℝ) * P w := by
    rw [Finsupp.sum]
    refine Finset.sum_nonneg fun w _ => mul_nonneg ?_ (hP w)
    have : 0 ≤ (D - D') w := by rw [Finsupp.sub_apply]; linarith [hle w]
    exact_mod_cast this
  linarith

end P2MJB

noncomputable section

namespace P2MJB

open AlgebraicCurve ModularCurve

section SAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_pow_of_mem (Q : Place K F) (hQ : Q.IsRational) {f : F} (hf : f ∈ Q.toValuationSubring) (n : ℕ) :
    Q.evalAt (f ^ n) = Q.evalAt f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Place.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, Q.evalAt_mul_of_mem hQ (pow_mem hf n) hf, ih]

theorem ne_zero_of_ord_eq_one (Q : Place K F) {t : F} (ht : Q.ord t = 1) : t ≠ 0 := by
  rintro rfl
  rw [Place.ord_zero] at ht
  exact zero_ne_one ht

theorem mem_of_ord_eq_zero (Q : Place K F) {f : F} (hf0 : f ≠ 0) (h : Q.ord f = 0) : f ∈ Q.toValuationSubring :=
  Q.mem_toValuationSubring_of_ord_nonneg_alt hf0 h.ge

theorem abv_sum_le_of_forall_le (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) {ι : Type*} (t : Finset ι)
    (g : ι → K) {C : ℝ} (hC : 0 ≤ C) (h : ∀ l ∈ t, μ (g l) ≤ C) : μ (∑ l ∈ t, g l) ≤ C := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hC
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (hμ _ _).trans (max_le (h a (Finset.mem_insert_self a t)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl)))

theorem abv_natCast_le_one (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) (n : ℕ) : μ (n : K) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (hμ _ _).trans (max_le ih (by rw [map_one]))

theorem abv_intCast_le_one (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ) (n : ℤ) : μ (n : K) ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.cast_natCast]; exact abv_natCast_le_one μ hμ m
  · rw [Int.cast_neg, Int.cast_natCast, μ.map_neg]; exact abv_natCast_le_one μ hμ m

theorem exists_forall_abv_le (μ : AbsoluteValue K ℝ) {r : ℕ} (hr : 0 < r) (x : Fin r → K) :
    ∃ i, ∀ l, μ (x l) ≤ μ (x i) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun l => μ (x l)) ⟨⟨0, hr⟩, Finset.mem_univ _⟩
  exact ⟨i, fun l => hi l (Finset.mem_univ l)⟩

theorem iSup_abv_eq_of_forall_le (μ : AbsoluteValue K ℝ) {r : ℕ} (x : Fin r → K) (i : Fin r)
    (hi : ∀ l, μ (x l) ≤ μ (x i)) : (⨆ l, μ (x l)) = μ (x i) :=
  haveI : Nonempty (Fin r) := ⟨i⟩
  le_antisymm (ciSup_le hi) (le_ciSup (f := fun l => μ (x l)) (Set.finite_range _).bddAbove i)

theorem mul_inv_pow_eq_sum_smul_prod {r : ℕ} (s : Fin r → F) {k : ℕ} (cf : (Fin k → Fin r) → K) (u : F)
    (hu : u = ∑ φ : Fin k → Fin r, cf φ • ∏ l, s (φ l)) (i : Fin r) :
    u * ((s i)⁻¹) ^ k = ∑ φ : Fin k → Fin r, cf φ • ∏ l, (s (φ l) * (s i)⁻¹) := by
  rw [hu, Finset.sum_mul]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [smul_mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem ratio_mem_of_forall_ord_le (w : Place K F) {r : ℕ} (s : Fin r → F) (hs0 : ∀ l, s l ≠ 0) (i : Fin r)
    (hi : ∀ l, w.ord (s i) ≤ w.ord (s l)) (l : Fin r) : s l * (s i)⁻¹ ∈ w.toValuationSubring :=
  w.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 l) (inv_ne_zero (hs0 i)))
    (by rw [Place.ord_mul _ (hs0 l) (inv_ne_zero (hs0 i)), Place.ord_inv]; linarith [hi l])

theorem prod_ratio_mem (w : Place K F) {r : ℕ} (s : Fin r → F) (hs0 : ∀ l, s l ≠ 0) (i : Fin r)
    (hi : ∀ l, w.ord (s i) ≤ w.ord (s l)) {k : ℕ} (φ : Fin k → Fin r) :
    (∏ l, (s (φ l) * (s i)⁻¹)) ∈ w.toValuationSubring :=
  prod_mem fun l _ => ratio_mem_of_forall_ord_le w s hs0 i hi (φ l)

theorem taylorCoeff_centre (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1) {f : F}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) {e : ℕ} (he : v.ord f = e) :
    (∀ q, q < e → v.taylorCoeff t q f = 0) ∧ v.taylorCoeff t e f = v.evalAt (f * t⁻¹ ^ e) ∧
      v.evalAt (f * t⁻¹ ^ e) ≠ 0 := by
  have h1 : ∀ q, q < e → v.taylorCoeff t q f = 0 :=
    (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord v hv ht hf hf0 e).mpr he.ge
  have h2 := Place.taylorCoeff_eq_evalAt_mul_inv_pow_of_forall_taylorCoeff_eq_zero v t f h1
  refine ⟨h1, h2, ?_⟩
  have h3 := Place.taylorCoeff_ord_ne_zero v hv ht hf hf0
  rw [he, Int.toNat_natCast] at h3
  rwa [h2] at h3

end SAux

section STwo

variable {N : ℕ} [NeZero N]

theorem ord_add_embDivisor_eq_zero_of_forall_ord_le {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r)
    (hi : ∀ l, w.ord (s i) ≤ w.ord (s l)) : w.ord (s i) + embDivisor N w = 0 := by
  obtain ⟨i₀, h0⟩ := exists_ord_add_embDivisor_eq_zero N s hs w
  have hsE : s i ∈ riemannRochSpace (embDivisor N) := hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  have h1 := ((mem_riemannRochSpace_iff.mp hsE) w).resolve_left (hs.1.ne_zero i)
  have h2 := hi i₀
  linarith

theorem ord_mul_inv_pow_eq {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r) (hi : ∀ l, w.ord (s i) ≤ w.ord (s l))
    {k : ℕ} {u : modularFunctionFieldBar N} (hu0 : u ≠ 0)
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) :
    w.ord (u * ((s i)⁻¹) ^ k) = B w := by
  have hs0 : ∀ l, s l ≠ 0 := fun l => hs.1.ne_zero l
  have hE : w.ord (s i) = -(embDivisor N w) := by
    have := ord_add_embDivisor_eq_zero_of_forall_ord_le s hs w i hi; linarith
  rw [hB w, Place.ord_mul _ hu0 (pow_ne_zero k (inv_ne_zero (hs0 i))), ← zpow_natCast, Place.ord_zpow, Place.ord_inv,
    Finsupp.smul_apply, smul_eq_mul, hE, neg_neg]

end STwo

section SNine

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 6400000 in

theorem log_abv_regVal_le_centre {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (hs0 : ∀ l, s l ≠ 0)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r) (hi : ∀ l, v₀.ord (s i) ≤ v₀.ord (s l))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hpiv : ∀ l, μ (evalVec s v₀ l) ≤ μ (evalVec s v₀ i))
    (c : Fin r → ℤ) (z tR : modularFunctionFieldBar N)
    (hz : z = ∑ m, (c m : AlgebraicClosure ℚ) • (s m * (s i)⁻¹))
    (htR : tR = z - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (v₀.evalAt z)) (htR1 : v₀.ord tR = 1)
    (k e : ℕ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0) (hfe : v₀.ord (u * ((s i)⁻¹) ^ k) = e)
    (t : modularFunctionFieldBar N) (ht : 0 < e → v₀.ord t = 1)
    (hy0 : 0 < e → (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))) ≠ 0) :
    Real.log (μ (regVal s v₀ t k e u))
      ≤ Real.log (μ (v₀.evalAt (u * ((s i)⁻¹) ^ k * tR⁻¹ ^ e)))
        + (k : ℝ) * Real.log (⨆ l, μ (evalVec s v₀ l))
        + (e : ℝ) * (Real.log (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)))
            - 2 * Real.log (⨆ l, μ (evalVec s v₀ l))) := by
  classical
  have hrat : v₀.IsRational := isRational_bar N v₀
  haveI : Nonempty (Fin r) := ⟨i⟩

  set piv := pivotIndex s v₀ hr with hpiv_def
  have hpivle : ∀ j, v₀.ord (s piv) ≤ v₀.ord (s j) := ord_pivot_le hr s v₀
  have hordip : v₀.ord (s i) = v₀.ord (s piv) := le_antisymm (hi piv) (hpivle i)
  have hx : ∀ l, evalVec s v₀ l = v₀.evalAt (s l * (s piv)⁻¹) := fun l => evalVec_apply hr s v₀ l
  have hmem_p : ∀ l, s l * (s piv)⁻¹ ∈ v₀.toValuationSubring := ratio_mem_of_forall_ord_le v₀ s hs0 piv hpivle
  have hmem_i : ∀ l, s l * (s i)⁻¹ ∈ v₀.toValuationSubring := ratio_mem_of_forall_ord_le v₀ s hs0 i hi
  have hip0 : s i * (s piv)⁻¹ ≠ 0 := mul_ne_zero (hs0 i) (inv_ne_zero (hs0 piv))
  have hord_ip : v₀.ord (s i * (s piv)⁻¹) = 0 := by
    rw [Place.ord_mul _ (hs0 i) (inv_ne_zero (hs0 piv)), Place.ord_inv, hordip]; ring
  have hxi0 : evalVec s v₀ i ≠ 0 := by
    rw [hx]; exact v₀.evalAt_ne_zero_of_ord_eq_zero hrat hip0 hord_ip
  set S : ℝ := ⨆ l, μ (evalVec s v₀ l) with hS
  have hSeq : S = μ (evalVec s v₀ i) := iSup_abv_eq_of_forall_le μ (evalVec s v₀) i hpiv
  have hS0 : 0 < S := by rw [hSeq]; exact μ.pos hxi0

  set f := u * ((s i)⁻¹) ^ k with hf
  have hf0 : f ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ (inv_ne_zero (hs0 i)))
  have htR0 : tR ≠ 0 := ne_zero_of_ord_eq_one v₀ htR1
  have hg0 : f * tR⁻¹ ^ e ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ (inv_ne_zero htR0))
  have hordg : v₀.ord (f * tR⁻¹ ^ e) = 0 := by
    rw [Place.ord_mul _ hf0 (pow_ne_zero _ (inv_ne_zero htR0)), ← zpow_natCast, Place.ord_zpow, Place.ord_inv, hfe, htR1]
    ring
  have hg_mem : f * tR⁻¹ ^ e ∈ v₀.toValuationSubring := mem_of_ord_eq_zero v₀ hg0 hordg
  have hcoef0 : v₀.evalAt (f * tR⁻¹ ^ e) ≠ 0 := v₀.evalAt_ne_zero_of_ord_eq_zero hrat hg0 hordg
  have hμcoef : 0 < μ (v₀.evalAt (f * tR⁻¹ ^ e)) := μ.pos hcoef0
  have hip_mem : s i * (s piv)⁻¹ ∈ v₀.toValuationSubring := hmem_p i

  have hevpow : v₀.evalAt ((s i * (s piv)⁻¹) ^ k) = (evalVec s v₀ i) ^ k := by
    rw [evalAt_pow_of_mem v₀ hrat hip_mem, ← hx i]
  rcases Nat.eq_zero_or_pos e with he | he
  ·
    subst he
    have hid : u * ((s piv)⁻¹) ^ k * t⁻¹ ^ 0 = (f * tR⁻¹ ^ 0) * (s i * (s piv)⁻¹) ^ k := by
      have h1 := hs0 i
      rw [hf, pow_zero, pow_zero, mul_one, mul_one, mul_assoc, ← mul_pow, inv_mul_cancel_left₀ h1]
    have hval : regVal s v₀ t k 0 u = v₀.evalAt (f * tR⁻¹ ^ 0) * (evalVec s v₀ i) ^ k := by
      rw [regVal_apply hr, hid, v₀.evalAt_mul_of_mem hrat hg_mem (pow_mem hip_mem k), hevpow]
    rw [hval, map_mul, map_pow, Real.log_mul hμcoef.ne' (pow_ne_zero _ (μ.pos hxi0).ne'), Real.log_pow, hSeq]
    push_cast
    linarith
  ·
    have ht1 : v₀.ord t = 1 := ht he
    have ht0 : t ≠ 0 := ne_zero_of_ord_eq_one v₀ ht1

    have hq0 : tR * t⁻¹ ≠ 0 := mul_ne_zero htR0 (inv_ne_zero ht0)
    have hordq : v₀.ord (tR * t⁻¹) = 0 := by rw [Place.ord_mul _ htR0 (inv_ne_zero ht0), Place.ord_inv, htR1, ht1]; ring
    have hq_mem : tR * t⁻¹ ∈ v₀.toValuationSubring := mem_of_ord_eq_zero v₀ hq0 hordq
    have hq_ev0 : v₀.evalAt (tR * t⁻¹) ≠ 0 := v₀.evalAt_ne_zero_of_ord_eq_zero hrat hq0 hordq
    have hμq : 0 < μ (v₀.evalAt (tR * t⁻¹)) := μ.pos hq_ev0

    have hid : u * ((s piv)⁻¹) ^ k * t⁻¹ ^ e = (f * tR⁻¹ ^ e) * (s i * (s piv)⁻¹) ^ k * (tR * t⁻¹) ^ e := by
      have h1 := hs0 i
      rw [hf, show u * (s i)⁻¹ ^ k * tR⁻¹ ^ e * (s i * (s piv)⁻¹) ^ k * (tR * t⁻¹) ^ e
          = u * ((s i)⁻¹ * (s i * (s piv)⁻¹)) ^ k * (tR⁻¹ * (tR * t⁻¹)) ^ e by ring,
        inv_mul_cancel_left₀ h1, inv_mul_cancel_left₀ htR0]
    have hval : regVal s v₀ t k e u
        = v₀.evalAt (f * tR⁻¹ ^ e) * (evalVec s v₀ i) ^ k * (v₀.evalAt (tR * t⁻¹)) ^ e := by
      rw [regVal_apply hr, hid, v₀.evalAt_mul_of_mem hrat (mul_mem hg_mem (pow_mem hip_mem k)) (pow_mem hq_mem e),
        v₀.evalAt_mul_of_mem hrat hg_mem (pow_mem hip_mem k), hevpow, evalAt_pow_of_mem v₀ hrat hq_mem]

    set Y : ℝ := ⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)) with hY
    have hYnn : 0 ≤ Y := by
      rw [hY]
      exact le_ciSup_of_le (Set.finite_range _).bddAbove (i, i) (apply_nonneg _ _)
    have hY0 : 0 < Y := lt_of_le_of_ne hYnn (fun h => hy0 he h.symm)
    have hbound : μ (v₀.evalAt (tR * t⁻¹)) ≤ Y / S ^ 2 := by

      set g : Fin r → modularFunctionFieldBar N :=
        fun m => (s m * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (v₀.evalAt (s m * (s i)⁻¹))) * t⁻¹ with hg
      have hd_mem : ∀ m, s m * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (v₀.evalAt (s m * (s i)⁻¹))
          ∈ v₀.toValuationSubring := fun m => sub_mem (hmem_i m) (v₀.algebraMap_mem' _)
      have hd_ev : ∀ m, v₀.evalAt (s m * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (v₀.evalAt (s m * (s i)⁻¹))) = 0 := by
        intro m
        rw [P2MW.evalAt_sub_of_mem v₀ hrat (hmem_i m) (v₀.algebraMap_mem' _), Place.evalAt_algebraMap_eq, sub_self]
      have hg_mem' : ∀ m, g m ∈ v₀.toValuationSubring := by
        intro m
        rcases eq_or_ne (s m * (s i)⁻¹ - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (v₀.evalAt (s m * (s i)⁻¹))) 0 with h0 | h0
        · have : g m = 0 := by simp only [hg, h0, zero_mul]
          rw [this]; exact zero_mem _
        · have hpos := P2MW.ord_pos_of_evalAt_eq_zero v₀ hrat h0 (hd_mem m) (hd_ev m)
          exact v₀.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero h0 (inv_ne_zero ht0))
            (by rw [Place.ord_mul _ h0 (inv_ne_zero ht0), Place.ord_inv, ht1]; omega)

      have hzev : v₀.evalAt z = ∑ m, (c m : AlgebraicClosure ℚ) * v₀.evalAt (s m * (s i)⁻¹) := by
        rw [hz]; exact P2MW.evalAt_sum_smul_of_mem _ v₀ hrat _ hmem_i
      have hqsum : tR * t⁻¹ = ∑ m, (c m : AlgebraicClosure ℚ) • g m := by
        rw [htR, hzev, map_sum, hz, ← Finset.sum_sub_distrib, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [hg, Algebra.smul_def, map_mul, map_intCast]
        ring

      have hYm : ∀ m, v₀.evalAt (s m * (s i)⁻¹) = evalVec s v₀ m * (evalVec s v₀ i)⁻¹ := by
        intro m
        have hprod : s m * (s piv)⁻¹ = (s m * (s i)⁻¹) * (s i * (s piv)⁻¹) := by
          rw [mul_assoc, inv_mul_cancel_left₀ (hs0 i)]
        have := v₀.evalAt_mul_of_mem hrat (hmem_i m) hip_mem
        rw [← hprod, ← hx m, ← hx i] at this
        rw [this, mul_inv_cancel_right₀ hxi0]
      have hkey : ∀ m, evalVec s v₀ i * evalVec s v₀ i * v₀.evalAt (g m)
          = regVal s v₀ t 1 1 (evalVec s v₀ i • s m - evalVec s v₀ m • s i) := by
        intro m
        have halg : (evalVec s v₀ i • s m - evalVec s v₀ m • s i) * ((s piv)⁻¹) ^ 1 * t⁻¹ ^ 1
            = evalVec s v₀ i • ((s i * (s piv)⁻¹) * g m) := by
          simp only [hg]
          rw [hYm m, pow_one, pow_one, map_mul, map_inv₀]
          simp only [Algebra.smul_def]
          have h1 := hs0 i
          have h3 : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s v₀ i) ≠ 0 := by
            rw [ne_eq, map_eq_zero_iff _ (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)).injective]; exact hxi0
          linear_combination
            (-(algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s v₀ i)) * s m * (s piv)⁻¹ * t⁻¹) * (mul_inv_cancel₀ h1)
            + (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (evalVec s v₀ m) * s i * (s piv)⁻¹ * t⁻¹) * (mul_inv_cancel₀ h3)
        rw [regVal_apply hr, halg, P2MW.evalAt_smul_of_mem v₀ hrat _ (mul_mem hip_mem (hg_mem' m)),
          v₀.evalAt_mul_of_mem hrat hip_mem (hg_mem' m), ← hx i, mul_assoc]
      have hgbd : ∀ m, μ (v₀.evalAt (g m)) ≤ Y / S ^ 2 := by
        intro m
        have hSi : μ (evalVec s v₀ i) = S := hSeq.symm
        have heq : v₀.evalAt (g m) = regVal s v₀ t 1 1 (evalVec s v₀ i • s m - evalVec s v₀ m • s i) / (evalVec s v₀ i) ^ 2 := by
          rw [eq_div_iff (pow_ne_zero 2 hxi0), ← hkey m]; ring
        rw [heq, map_div₀, map_pow, hSi]
        refine div_le_div_of_nonneg_right ?_ (pow_nonneg hS0.le 2)
        rw [hY]
        exact le_ciSup (f := fun q : Fin r × Fin r => μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)))
          (Set.finite_range _).bddAbove (i, m)
      have hsum_ev : v₀.evalAt (tR * t⁻¹) = ∑ m, (c m : AlgebraicClosure ℚ) * v₀.evalAt (g m) := by
        rw [hqsum]; exact P2MW.evalAt_sum_smul_of_mem _ v₀ hrat _ hg_mem'
      rw [hsum_ev]
      refine abv_sum_le_of_forall_le μ hμ _ _ (div_nonneg hYnn (pow_nonneg hS0.le 2)) fun m _ => ?_
      rw [map_mul]
      calc μ ((c m : AlgebraicClosure ℚ)) * μ (v₀.evalAt (g m)) ≤ 1 * (Y / S ^ 2) :=
            mul_le_mul (abv_intCast_le_one μ hμ (c m)) (hgbd m) (apply_nonneg _ _) zero_le_one
        _ = Y / S ^ 2 := one_mul _

    have hlogq : Real.log (μ (v₀.evalAt (tR * t⁻¹))) ≤ Real.log Y - 2 * Real.log S := by
      have h := Real.log_le_log hμq hbound
      rw [Real.log_div hY0.ne' (pow_ne_zero _ hS0.ne'), Real.log_pow] at h
      push_cast at h
      linarith
    rw [hval, map_mul, map_mul, map_pow, map_pow,
      Real.log_mul (mul_ne_zero hμcoef.ne' (pow_ne_zero _ (μ.pos hxi0).ne')) (pow_ne_zero _ hμq.ne'),
      Real.log_mul hμcoef.ne' (pow_ne_zero _ (μ.pos hxi0).ne'), Real.log_pow, Real.log_pow, ← hSeq]
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have hmul := mul_le_mul_of_nonneg_left hlogq he0
    linarith

end SNine

end P2MJB

end

noncomputable section

namespace P2MJB

open AlgebraicCurve

section TaylorHom

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def taylorSeries (v : Place K F) (t : F) (f : F) : PowerSeries K :=
  PowerSeries.mk fun n => v.taylorCoeff t n f

theorem coeff_taylorSeries (v : Place K F) (t : F) (f : F) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries v t f) = v.taylorCoeff t n f := by
  rw [taylorSeries, PowerSeries.coeff_mk]

variable (v : Place K F) (hv : v.IsRational) {t : F} (ht : v.ord t = 1)
include hv ht

theorem taylorSeries_add {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    taylorSeries v t (f + g) = taylorSeries v t f + taylorSeries v t g := by
  ext n
  rw [map_add, coeff_taylorSeries, coeff_taylorSeries, coeff_taylorSeries, Place.taylorCoeff_add v hv ht hf hg n]

theorem taylorSeries_mul {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    taylorSeries v t (f * g) = taylorSeries v t f * taylorSeries v t g := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_taylorSeries, Place.taylorCoeff_mul v hv ht hf hg n]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_taylorSeries, coeff_taylorSeries]

theorem taylorSeries_smul {f : F} (hf : f ∈ v.toValuationSubring) (a : K) :
    taylorSeries v t (a • f) = PowerSeries.C a * taylorSeries v t f := by
  ext n
  rw [PowerSeries.coeff_C_mul, coeff_taylorSeries, coeff_taylorSeries, Place.taylorCoeff_smul v hv ht hf a n]

omit hv ht in
theorem taylorSeries_one : taylorSeries v t (1 : F) = 1 := by
  ext n
  rw [coeff_taylorSeries, PowerSeries.coeff_one]
  have h := Place.taylorCoeff_algebraMap v t (1 : K) n
  rwa [map_one] at h

omit hv ht in
theorem taylorSeries_zero : taylorSeries v t (0 : F) = 0 := by
  ext n
  rw [coeff_taylorSeries, map_zero]
  have h := Place.taylorCoeff_algebraMap v t (0 : K) n
  rw [map_zero] at h
  rw [h]; split_ifs <;> rfl

theorem taylorSeries_prod {ι : Type*} (S : Finset ι) (g : ι → F) (hg : ∀ j ∈ S, g j ∈ v.toValuationSubring) :
    taylorSeries v t (∏ j ∈ S, g j) = ∏ j ∈ S, taylorSeries v t (g j) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty]; exact taylorSeries_one v
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      taylorSeries_mul v hv ht (hg a (Finset.mem_insert_self a S)) (prod_mem fun j hj => hg j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

theorem taylorSeries_sum {ι : Type*} (S : Finset ι) (g : ι → F) (hg : ∀ j ∈ S, g j ∈ v.toValuationSubring) :
    taylorSeries v t (∑ j ∈ S, g j) = ∑ j ∈ S, taylorSeries v t (g j) := by
  classical
  induction S using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact taylorSeries_zero v
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      taylorSeries_add v hv ht (hg a (Finset.mem_insert_self a S)) (sum_mem fun j hj => hg j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_insert_of_mem hj)]

theorem taylorSeries_sum_smul_prod {r k : ℕ} (Y : Fin r → F) (hY : ∀ l, Y l ∈ v.toValuationSubring)
    (cf : (Fin k → Fin r) → K) :
    taylorSeries v t (∑ φ : Fin k → Fin r, cf φ • ∏ l, Y (φ l))
      = ∑ φ : Fin k → Fin r, PowerSeries.C (cf φ) * ∏ l, taylorSeries v t (Y (φ l)) := by
  rw [taylorSeries_sum v hv ht _ _ (fun φ _ => P2MW.smul_mem_of_mem v _ (prod_mem fun l _ => hY (φ l)))]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [taylorSeries_smul v hv ht (prod_mem fun l _ => hY (φ l)), taylorSeries_prod v hv ht _ _ (fun l _ => hY (φ l))]

end TaylorHom

end P2MJB

end

noncomputable section

namespace P2MJB

open AlgebraicCurve ModularCurve

section SEight

variable {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem sum_add_apply_le_sum (B B' : Divisor (AlgebraicClosure ℚ) F) (v₀ : Place (AlgebraicClosure ℚ) F)
    (hB0 : ∀ w, 0 ≤ B w) (hB'0 : ∀ w, 0 ≤ B' w) (hle : ∀ w, B' w ≤ (B.erase v₀) w) :
    (B'.sum fun _ n => (n : ℝ)) + (B v₀ : ℝ) ≤ B.sum fun _ n => (n : ℝ) := by
  classical
  have h1 : (B'.sum fun w n => (n : ℝ) * (fun _ => (1 : ℝ)) w) ≤ (B.erase v₀).sum fun w n => (n : ℝ) * (fun _ => (1 : ℝ)) w :=
    sum_le_sum_of_le' (B.erase v₀) B' hB'0 hle (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
  simp only [mul_one] at h1
  have h2 := Finsupp.add_sum_erase' B v₀ (fun _ n => (n : ℝ)) (fun w => by simp)
  linarith

theorem ball_split_le (B' : Divisor (AlgebraicClosure ℚ) F) (hB'0 : ∀ w, 0 ≤ B' w)
    (ball : Place (AlgebraicClosure ℚ) F → Prop) [DecidablePred ball] (P δ : Place (AlgebraicClosure ℚ) F → ℝ) (Λ : ℝ)
    (hin : ∀ w ∈ B'.support, ball w → δ w ≤ -P w) (hout : ∀ w ∈ B'.support, ¬ ball w → P w ≤ Λ) :
    (∑ w ∈ B'.support.filter ball, (B' w : ℝ) * (δ w + Λ))
      ≤ -(B'.sum fun w n => (n : ℝ) * P w) + (B'.sum fun _ n => (n : ℝ)) * Λ := by
  classical
  rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_filter_add_sum_filter_not B'.support ball (fun w => (B' w : ℝ) * P w),
    ← Finset.sum_filter_add_sum_filter_not B'.support ball (fun w => (B' w : ℝ)), add_mul, Finset.sum_mul, Finset.sum_mul]
  have hA : ∑ w ∈ B'.support.filter ball, (B' w : ℝ) * (δ w + Λ)
      ≤ ∑ w ∈ B'.support.filter ball, (-( (B' w : ℝ) * P w) + (B' w : ℝ) * Λ) := by
    refine Finset.sum_le_sum fun w hw => ?_
    rw [Finset.mem_filter] at hw
    have hBw : (0 : ℝ) ≤ B' w := by exact_mod_cast hB'0 w
    nlinarith [hin w hw.1 hw.2]
  have hB : (0 : ℝ) ≤ ∑ w ∈ B'.support.filter (fun w => ¬ ball w), (-((B' w : ℝ) * P w) + (B' w : ℝ) * Λ) := by
    refine Finset.sum_nonneg fun w hw => ?_
    rw [Finset.mem_filter] at hw
    have hBw : (0 : ℝ) ≤ B' w := by exact_mod_cast hB'0 w
    nlinarith [hout w hw.1 hw.2]
  rw [Finset.sum_add_distrib] at hA hB
  simp only [Finset.sum_neg_distrib] at hA hB
  linarith
end SEight

section ChartVocab

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

def chartFun {r : ℕ} (s : Fin r → F) (i : Fin r) (c : Fin r → ℤ) : F :=
  ∑ m, (c m : AlgebraicClosure ℚ) • (s m * (s i)⁻¹)

def chartUnif {r : ℕ} (s : Fin r → F) (i : Fin r) (c : Fin r → ℤ) (w : Place (AlgebraicClosure ℚ) F) : F :=
  chartFun s i c - algebraMap (AlgebraicClosure ℚ) F (w.evalAt (chartFun s i c))

def lam (n₀ : ℕ) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (p : ℕ) : ℝ :=
  (n₀ : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))

def inBall {r : ℕ} (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (s : Fin r → F) (R : Place (AlgebraicClosure ℚ) F) (Λ : ℝ)
    (w : Place (AlgebraicClosure ℚ) F) : Prop :=
  w = R ∨ Λ < prox μ (evalVec s R) (evalVec s w)

theorem lam_nonneg (n₀ : ℕ) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (p : ℕ) (hμp : μ (p : AlgebraicClosure ℚ) < 1) :
    0 ≤ lam n₀ μ p :=
  mul_nonneg (Nat.cast_nonneg _) (neg_nonneg.mpr (Real.log_nonpos (apply_nonneg _ _) hμp.le))

end ChartVocab

def ChartSpec (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (p n₀ : ℕ)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r)
    (c : Fin r → ℤ) : Prop :=

  (∀ w, inBall μ s R (lam n₀ μ p) w →
      (∀ l, w.ord (s i) ≤ w.ord (s l)) ∧ w.ord (chartUnif s i c w) = 1) ∧

  (∀ l n, μ (R.taylorCoeff (chartUnif s i c R) n (s l * (s i)⁻¹)) * (μ (p : AlgebraicClosure ℚ) ^ n₀) ^ n ≤ 1) ∧

  (∀ w w', inBall μ s R (lam n₀ μ p) w → inBall μ s R (lam n₀ μ p) w' → w ≠ w' →
      w.evalAt (chartFun s i c) ≠ w'.evalAt (chartFun s i c) ∧
      prox μ (evalVec s w) (evalVec s w') ≤ -Real.log (μ (w.evalAt (chartFun s i c) - w'.evalAt (chartFun s i c)))) ∧

  (∀ (L : Type) [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
      (ι : AlgebraicClosure ℚ →+* L), (∀ x, ‖ι x‖ = μ x) →
      ∀ w, inBall μ s R (lam n₀ μ p) w → ∀ l,
        PowerSeries.map ι (PowerSeries.mk fun n => w.taylorCoeff (chartUnif s i c w) n (s l * (s i)⁻¹))
          = (PowerSeries.mk fun n => ∑' kk : ℕ,
              PowerSeries.coeff (n + kk) (PowerSeries.map ι (PowerSeries.mk fun n => R.taylorCoeff (chartUnif s i c R) n (s l * (s i)⁻¹)))
                * ((n + kk).choose n : L) * (ι (w.evalAt (chartFun s i c) - R.evalAt (chartFun s i c))) ^ kk))

section STen

variable {N : ℕ} [NeZero N]

open Classical in
set_option maxHeartbeats 6400000 in
theorem discLine_mu {r : ℕ} (hr : 0 < r) (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (p : ℕ) (n₀ : ℕ) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ)
    (hμp : μ (p : AlgebraicClosure ℚ) < 1)
    {k : ℕ} (cf : (Fin k → Fin r) → AlgebraicClosure ℚ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0)
    (hurep : u = ∑ φ : Fin k → Fin r, cf φ • ∏ l, s (φ l))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB'0 : ∀ w, 0 ≤ B' w) (hB'le : ∀ w, B' w ≤ (B.erase v₀) w)
    (i : Fin r) (hpiv : ∀ l, μ (evalVec s v₀ l) ≤ μ (evalVec s v₀ i)) (c : Fin r → ℤ)
    (hUi : ∀ l, v₀.ord (s i) ≤ v₀.ord (s l)) (hUt : v₀.ord (chartUnif s i c v₀) = 1)
    (hC2 : ∀ w ∈ B'.support, inBall μ s v₀ (lam n₀ μ p) w →
      Real.log (μ (w.evalAt (chartFun s i c) - v₀.evalAt (chartFun s i c))) ≤ -prox μ (evalVec s v₀) (evalVec s w))
    (t : modularFunctionFieldBar N) (ht : 0 < B v₀ → v₀.ord t = 1)
    (hy0 : 0 < B v₀ → (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))) ≠ 0)
    (hcore : Real.log (μ (v₀.evalAt (u * ((s i)⁻¹) ^ k * (chartUnif s i c v₀)⁻¹ ^ (B v₀).toNat)))
        ≤ Real.log (⨆ φ, μ (cf φ)) + ((B v₀).toNat : ℝ) * lam n₀ μ p
          + ∑ w ∈ B'.support.filter (fun w => inBall μ s v₀ (lam n₀ μ p) w),
              (B' w : ℝ) * (Real.log (μ (w.evalAt (chartFun s i c) - v₀.evalAt (chartFun s i c))) + lam n₀ μ p)) :
    Real.log (μ (regVal s v₀ t k (B v₀).toNat u))
      ≤ Real.log (⨆ φ, μ (cf φ))
        + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ l, μ (evalVec s v₀ l))
        + (B v₀ : ℝ) * Real.log (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)))
        - (B'.sum fun w n => (n : ℝ) * prox μ (evalVec s v₀) (evalVec s w))
        + ((embDegree N : ℝ) * n₀) * k * (-Real.log (μ (p : AlgebraicClosure ℚ))) := by
  classical
  have hs0 : ∀ l, s l ≠ 0 := fun l => hs.1.ne_zero l
  have hsE : ∀ l, s l ∈ riemannRochSpace (embDivisor N) := fun l => hs.2 ▸ Submodule.subset_span ⟨l, rfl⟩
  have hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) := mem_rr_of_monomialRep' (embDivisor N) s hsE cf u hurep
  have hBnn : ∀ w, 0 ≤ B w := effective_of_mem hu0 hu B hB
  set e : ℕ := (B v₀).toNat with he_def
  have he : (e : ℤ) = B v₀ := Int.toNat_of_nonneg (hBnn v₀)
  have heR : (e : ℝ) = (B v₀ : ℝ) := by exact_mod_cast he
  have hepos : 0 < e ↔ 0 < B v₀ := by omega
  have hfe : v₀.ord (u * ((s i)⁻¹) ^ k) = e := by rw [ord_mul_inv_pow_eq s hs v₀ i hUi hu0 B hB, he]

  have h9 := log_abv_regVal_le_centre hr s hs0 v₀ i hUi μ hμ hpiv c (chartFun s i c) (chartUnif s i c v₀) rfl rfl hUt
    k e u hu0 hfe t (fun h => ht (hepos.mp h)) (fun h => hy0 (hepos.mp h))

  have h8 := ball_split_le B' hB'0 (fun w => inBall μ s v₀ (lam n₀ μ p) w)
    (fun w => prox μ (evalVec s v₀) (evalVec s w))
    (fun w => Real.log (μ (w.evalAt (chartFun s i c) - v₀.evalAt (chartFun s i c)))) (lam n₀ μ p) hC2
    (fun w _ hw => not_lt.mp fun h => hw (Or.inr h))

  obtain ⟨Du, hDu, hDudeg⟩ := (hasPrincipalDivisors_modularFunctionFieldBar_unconditional N).exists_divisor u hu0
  have hBmass : B.sum (fun _ n => (n : ℝ)) = (k : ℝ) * embDegree N := mass_eq hu0 B hB Du hDu hDudeg
  have hmass := sum_add_apply_le_sum B B' v₀ hBnn hB'0 hB'le
  have hΛ0 : 0 ≤ lam n₀ μ p := lam_nonneg n₀ μ p hμp
  have hB'mass0 : 0 ≤ B'.sum fun _ n => (n : ℝ) := by
    rw [Finsupp.sum]; exact Finset.sum_nonneg fun w _ => by exact_mod_cast hB'0 w
  have hcharge : ((e : ℝ) + B'.sum fun _ n => (n : ℝ)) * lam n₀ μ p ≤ (k : ℝ) * embDegree N * lam n₀ μ p :=
    mul_le_mul_of_nonneg_right (by linarith) hΛ0
  have hΛ : (embDegree N : ℝ) * n₀ * k * (-Real.log (μ (p : AlgebraicClosure ℚ))) = (k : ℝ) * embDegree N * lam n₀ μ p := by
    unfold lam; ring
  rw [hΛ, ← heR]
  nlinarith [h9, h8, hcore, hcharge, hΛ0, hB'mass0]

end STen

section Assembly

open Classical in
set_option maxHeartbeats 6400000 in

theorem jensen_bad_at_le_of_chart (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (S₀ : Finset ℕ)
    (hC1 : ∀ p : ℕ, p.Prime → ∃ n₀ : ℕ, ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 → ∀ (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r),
      (∀ l, μ (evalVec s R l) ≤ μ (evalVec s R i)) → ∃ c : Fin r → ℤ, ChartSpec N s p n₀ μ R i c)
    (hcore : ∀ (p n₀ : ℕ), p.Prime → ∀ (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ), IsNonarchimedean μ → μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r),
      (∀ l, μ (evalVec s v₀ l) ≤ μ (evalVec s v₀ i)) → ∀ c : Fin r → ℤ, ChartSpec N s p n₀ μ v₀ i c →
      ∀ (k : ℕ) (cf : (Fin k → Fin r) → AlgebraicClosure ℚ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, cf φ • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      Real.log (μ (v₀.evalAt (u * ((s i)⁻¹) ^ k * (chartUnif s i c v₀)⁻¹ ^ (B v₀).toNat)))
        ≤ Real.log (⨆ φ, μ (cf φ)) + ((B v₀).toNat : ℝ) * lam n₀ μ p
          + ∑ w ∈ B'.support.filter (fun w => inBall μ s v₀ (lam n₀ μ p) w),
              (B' w : ℝ) * (Real.log (μ (w.evalAt (chartFun s i c) - v₀.evalAt (chartFun s i c))) + lam n₀ μ p)) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k * (-Real.log (ν (p : ↥L))) := by
  classical

  choose n0 hn0 using hC1
  let Nof : ℕ → ℕ := fun p => if hp : p.Prime then n0 p hp else 0
  set Nmax : ℕ := ∑ p ∈ S₀, Nof p with hNmax
  have hNmax : ∀ p ∈ S₀, ∀ hp : p.Prime, n0 p hp ≤ Nmax := by
    intro p hpS hp
    have h1 : Nof p ≤ Nmax := Finset.single_le_sum (fun q _ => Nat.zero_le (Nof q)) hpS
    have h2 : n0 p hp = Nof p := by show n0 p hp = (if hp : p.Prime then n0 p hp else 0); rw [dif_pos hp]
    omega
  set d : ℝ := (embDegree N : ℝ) with hd
  refine ⟨d * Nmax, ?_⟩
  intro k L _ cL u hu0 hurep B hB ν p hp hpS hνp v₀ B' hB'0 hB'le x hx hx₀ t ht a ha y hy hy0
  obtain ⟨μ, hμ, hμν⟩ := NumberField.exists_isNonarchimedean_absoluteValue_extends L ν
  have hcast : (((p : ℕ) : ↥L) : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) := by norm_cast
  have hνμp : ν (p : ↥L) = μ (p : AlgebraicClosure ℚ) := by rw [← hμν, hcast]
  have hμp : μ (p : AlgebraicClosure ℚ) < 1 := hνμp ▸ hνp
  set lam' : ℝ := -Real.log (μ (p : AlgebraicClosure ℚ)) with hlam'_def
  have hlam'0 : 0 ≤ lam' := by
    rw [hlam'_def, neg_nonneg]; exact Real.log_nonpos (apply_nonneg _ _) hμp.le

  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsE : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => hs.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨i₀, -⟩ := exists_ord_add_embDivisor_eq_zero N s hs (cuspInftyBar N)
  have hr : 0 < r := i₀.pos
  have hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) :=
    mem_rr_of_monomialRep' (embDivisor N) s hsE (fun φ => ((cL φ : ↥L) : AlgebraicClosure ℚ)) u hurep
  have hBnn : ∀ w, 0 ≤ B w := effective_of_mem hu0 hu B hB

  obtain ⟨i, hpiv⟩ := exists_forall_abv_le μ hr (evalVec s v₀)
  obtain ⟨c, hspec⟩ := hn0 p hp μ hμ hμp v₀ i hpiv
  obtain ⟨hU, hA, hC, hBm⟩ := hspec
  have hball0 : inBall μ s v₀ (lam (n0 p hp) μ p) v₀ := Or.inl rfl
  obtain ⟨hUi, hUt⟩ := hU v₀ hball0

  have hB'v₀ : B' v₀ = 0 := by
    have h1 := hB'le v₀; rw [Finsupp.erase_same] at h1; exact le_antisymm h1 (hB'0 v₀)
  have hC2 : ∀ w ∈ B'.support, inBall μ s v₀ (lam (n0 p hp) μ p) w →
      Real.log (μ (w.evalAt (chartFun s i c) - v₀.evalAt (chartFun s i c))) ≤ -prox μ (evalVec s v₀) (evalVec s w) := by
    intro w hw hball
    have hne : v₀ ≠ w := by
      intro h; rw [← h, Finsupp.mem_support_iff] at hw; exact hw hB'v₀
    obtain ⟨hinj, hle⟩ := hC v₀ w hball0 hball hne
    have hpos : 0 < μ (v₀.evalAt (chartFun s i c) - w.evalAt (chartFun s i c)) := μ.pos (sub_ne_zero.mpr hinj)
    rw [← μ.map_neg, neg_sub] at hpos hle
    linarith

  have hy0μ : 0 < B v₀ → (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1))) ≠ 0 := by
    intro hpos
    have hsupy : (⨆ q, ν (y q))
        = ⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)) := by
      congr 1; funext q; rw [← hμν, hy hpos q]
    rw [← hsupy]; exact hy0 hpos

  have hline := discLine_mu hr s hs p (n0 p hp) μ hμ hμp (fun φ => ((cL φ : ↥L) : AlgebraicClosure ℚ)) u hu0 hurep B hB v₀ B'
    hB'0 hB'le i hpiv c hUi hUt hC2 t ht hy0μ
    (hcore p (n0 p hp) hp μ hμ hμp v₀ i hpiv c ⟨hU, hA, hC, hBm⟩ k _ u hu0 hurep B hB B' hB'0 hB'le)

  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hn0le : ((n0 p hp : ℕ) : ℝ) ≤ (Nmax : ℝ) := by exact_mod_cast hNmax p hpS hp
  have hbd : (d * (n0 p hp : ℕ)) * k * lam' ≤ (d * Nmax) * k * lam' := by
    have := mul_le_mul_of_nonneg_left hn0le hd0
    have := mul_le_mul_of_nonneg_right this hk0
    exact mul_le_mul_of_nonneg_right this hlam'0
  have hμform : Real.log (μ (regVal s v₀ t k (B v₀).toNat u))
      ≤ Real.log (⨆ φ, μ (((cL φ : ↥L) : AlgebraicClosure ℚ)))
        + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, μ (evalVec s v₀ i))
        + (B v₀ : ℝ) * Real.log (⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)))
        - (B'.sum fun w n => (n : ℝ) * prox μ (evalVec s v₀) (evalVec s w))
        + (d * Nmax) * k * lam' := by
    rw [hd] at hbd ⊢; linarith [hline, hbd]

  have hval : ν a = μ (regVal s v₀ t k (B v₀).toNat u) := by rw [← hμν, ha]
  have hsupx : (⨆ i, ν (x v₀ i)) = ⨆ i, μ (evalVec s v₀ i) := by
    congr 1; funext i; rw [← hμν, hx₀]
  have hsupc : (⨆ φ, ν (cL φ)) = ⨆ φ, μ (((cL φ : ↥L) : AlgebraicClosure ℚ)) := by
    congr 1; funext φ; rw [← hμν]
  have hsum : (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
      = B'.sum fun w n => (n : ℝ) * prox μ (evalVec s v₀) (evalVec s w) := by
    unfold Finsupp.sum
    refine Finset.sum_congr rfl fun w hw => ?_
    show (B' w : ℝ) * prox ν (x v₀) (x w) = (B' w : ℝ) * prox μ (evalVec s v₀) (evalVec s w)
    rw [prox_coe ν μ hμν (x v₀) (x w) (evalVec s v₀) (evalVec s w) hx₀ (hx w hw)]
  rw [hval, hsupx, hsupc, hsum, hνμp, ← hlam'_def]
  by_cases he : B v₀ = 0
  · rw [he] at hμform ⊢
    push_cast at hμform ⊢
    simp only [mul_zero, zero_mul, sub_zero, add_zero] at hμform ⊢
    linarith [hμform]
  · have hepos : 0 < B v₀ := lt_of_le_of_ne (hBnn v₀) (Ne.symm he)
    have hsupy : (⨆ q, ν (y q))
        = ⨆ q : Fin r × Fin r, μ (regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)) := by
      congr 1; funext q; rw [← hμν, hy hepos q]
    rw [hsupy]
    linarith [hμform]

end Assembly

end P2MJB

end

namespace P2MJB

section ZerosMultiset

variable {α β : Type*} [DecidableEq β]

def zerosMultiset (T : Finset α) (m : α → ℕ) (a : α → β) : Multiset β :=
  T.val.bind fun w => Multiset.replicate (m w) (a w)

theorem exists_of_mem_zerosMultiset (T : Finset α) (m : α → ℕ) (a : α → β) {x : β}
    (hx : x ∈ zerosMultiset T m a) : ∃ w ∈ T, x = a w := by
  unfold zerosMultiset at hx
  rw [Multiset.mem_bind] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  exact ⟨w, hw, Multiset.eq_of_mem_replicate hxw⟩

theorem count_zerosMultiset (T : Finset α) (m : α → ℕ) (a : α → β) (hinj : Set.InjOn a T) {w : α} (hw : w ∈ T) :
    (zerosMultiset T m a).count (a w) = m w := by
  classical
  unfold zerosMultiset
  rw [Multiset.count_bind]
  have : (Multiset.map (fun b => Multiset.count (a w) (Multiset.replicate (m b) (a b))) T.val).sum
      = ∑ b ∈ T, (if a b = a w then m b else 0) := by
    rw [Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    rw [Multiset.count_replicate]
  rw [this]
  have h2 : ∀ b ∈ T, (if a b = a w then m b else 0) = (if b = w then m b else 0) := by
    intro b hb
    by_cases hbw : b = w
    · simp [hbw]
    · have : a b ≠ a w := fun h => hbw (hinj hb hw h)
      simp [this, hbw]
  rw [Finset.sum_congr rfl h2, Finset.sum_ite_eq' T w m, if_pos hw]

theorem prod_map_zerosMultiset {M : Type*} [CommMonoid M] (T : Finset α) (m : α → ℕ) (a : α → β) (g : β → M) :
    ((zerosMultiset T m a).map g).prod = ∏ w ∈ T, g (a w) ^ (m w) := by
  unfold zerosMultiset
  rw [Multiset.map_bind, Multiset.prod_bind, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun w _ => ?_
  rw [Multiset.map_replicate, Multiset.prod_replicate]

theorem log_prod_pow_eq_sum (T : Finset α) (m : α → ℕ) (g : α → ℝ) (hg : ∀ w ∈ T, 0 < g w) :
    Real.log (∏ w ∈ T, g w ^ (m w)) = ∑ w ∈ T, (m w : ℝ) * Real.log (g w) := by
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [Real.log_pow]
  · intro w hw; exact pow_ne_zero _ (hg w hw).ne'

end ZerosMultiset

end P2MJB

noncomputable section

namespace P2MJB

open AlgebraicCurve ModularCurve

section Core

variable {N : ℕ} [NeZero N]

open Classical in
set_option maxHeartbeats 6400000 in
theorem core_coeff_bound {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (p : ℕ) (hp : p.Prime) (n₀ : ℕ) (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ)
    (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (i : Fin r)
    (c : Fin r → ℤ) (hspec : ChartSpec N s p n₀ μ v₀ i c)
    {k : ℕ} (cf : (Fin k → Fin r) → AlgebraicClosure ℚ) (u : modularFunctionFieldBar N) (hu0 : u ≠ 0)
    (hurep : u = ∑ φ : Fin k → Fin r, cf φ • ∏ l, s (φ l))
    (B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB : ∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w)
    (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hB'0 : ∀ w, 0 ≤ B' w) (hB'le : ∀ w, B' w ≤ (B.erase v₀) w)
    (Lc : Type) [NontriviallyNormedField Lc] [CompleteSpace Lc] [IsUltrametricDist Lc]
    (ι : AlgebraicClosure ℚ →+* Lc) (hι : ∀ x, ‖ι x‖ = μ x)
    (hGauss : ∀ (cc : (Fin k → Fin r) → Lc) (G : (Fin k → Fin r) → Fin k → PowerSeries Lc) {ρ M : ℝ}, 0 ≤ ρ → 0 ≤ M →
      (∀ φ ∈ (Finset.univ : Finset (Fin k → Fin r)), ∀ j n, ‖PowerSeries.coeff n (G φ j)‖ * ρ ^ n ≤ 1) →
      (∀ φ ∈ (Finset.univ : Finset (Fin k → Fin r)), ‖cc φ‖ ≤ M) →
      ∀ n, ‖PowerSeries.coeff n (∑ φ ∈ Finset.univ, PowerSeries.C (cc φ) * ∏ j, G φ j)‖ * ρ ^ n ≤ M)
    (hShift : ∀ (cc : (Fin k → Fin r) → Lc) (G : (Fin k → Fin r) → Fin k → PowerSeries Lc) {ρ : ℝ}, 0 < ρ →
      (∀ φ ∈ (Finset.univ : Finset (Fin k → Fin r)), ∀ j n, ‖PowerSeries.coeff n (G φ j)‖ * ρ ^ n ≤ 1) →
      ∀ a : Lc, ‖a‖ < ρ →
      (PowerSeries.mk fun n => ∑' kk : ℕ, PowerSeries.coeff (n + kk) (∑ φ ∈ Finset.univ, PowerSeries.C (cc φ) * ∏ j, G φ j)
          * ((n + kk).choose n : Lc) * a ^ kk)
        = ∑ φ ∈ Finset.univ, PowerSeries.C (cc φ) * ∏ j, (PowerSeries.mk fun n => ∑' kk : ℕ,
            PowerSeries.coeff (n + kk) (G φ j) * ((n + kk).choose n : Lc) * a ^ kk)) :
    Real.log (μ (v₀.evalAt (u * ((s i)⁻¹) ^ k * (chartUnif s i c v₀)⁻¹ ^ (B v₀).toNat)))
      ≤ Real.log (⨆ φ, μ (cf φ)) + ((B v₀).toNat : ℝ) * lam n₀ μ p
        + ∑ w ∈ B'.support.filter (fun w => inBall μ s v₀ (lam n₀ μ p) w),
            (B' w : ℝ) * (Real.log (μ (w.evalAt (chartFun s i c) - v₀.evalAt (chartFun s i c))) + lam n₀ μ p) := by
  classical
  obtain ⟨hU, hA, hC, hBm⟩ := hspec
  have hs0 : ∀ l, s l ≠ 0 := fun l => hs.1.ne_zero l
  have hball0 : inBall μ s v₀ (lam n₀ μ p) v₀ := Or.inl rfl
  obtain ⟨hUi, hUt⟩ := hU v₀ hball0
  have hrat : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.IsRational := isRational_bar N
  haveI : Nonempty (Fin k → Fin r) := ⟨fun _ => i⟩

  set Λ : ℝ := lam n₀ μ p with hΛ
  set ρ : ℝ := μ (p : AlgebraicClosure ℚ) ^ n₀ with hρ_def
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hμp0 : 0 < μ (p : AlgebraicClosure ℚ) := μ.pos hp0
  have hρ : 0 < ρ := pow_pos hμp0 n₀
  have hlogρ : Real.log ρ = -Λ := by rw [hρ_def, Real.log_pow, hΛ]; unfold lam; ring

  set Y : Fin r → modularFunctionFieldBar N := fun l => s l * (s i)⁻¹ with hY
  have hYmem : ∀ l, Y l ∈ v₀.toValuationSubring := ratio_mem_of_forall_ord_le v₀ s hs0 i hUi
  set z : modularFunctionFieldBar N := chartFun s i c with hz
  set tR : modularFunctionFieldBar N := chartUnif s i c v₀ with htR
  have hfrep : u * ((s i)⁻¹) ^ k = ∑ φ : Fin k → Fin r, cf φ • ∏ l, Y (φ l) :=
    mul_inv_pow_eq_sum_smul_prod s cf u hurep i
  have hf0 : u * ((s i)⁻¹) ^ k ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ (inv_ne_zero (hs0 i)))
  have hsE : ∀ l, s l ∈ riemannRochSpace (embDivisor N) := fun l => hs.2 ▸ Submodule.subset_span ⟨l, rfl⟩
  have hu : u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) := mem_rr_of_monomialRep' (embDivisor N) s hsE cf u hurep
  have hBnn : ∀ w, 0 ≤ B w := effective_of_mem hu0 hu B hB
  set e : ℕ := (B v₀).toNat with he_def
  have he : (e : ℤ) = B v₀ := Int.toNat_of_nonneg (hBnn v₀)
  have hfe : v₀.ord (u * ((s i)⁻¹) ^ k) = e := by rw [ord_mul_inv_pow_eq s hs v₀ i hUi hu0 B hB, he]
  have hfmem : u * ((s i)⁻¹) ^ k ∈ v₀.toValuationSubring :=
    P2MW.mem_of_eq_zero_or_ord_nonneg v₀ (Or.inr (by rw [hfe]; exact_mod_cast Nat.zero_le e))
  obtain ⟨hvan, hcoefe, hcoefe0⟩ := taylorCoeff_centre v₀ (hrat v₀) hUt hfmem hf0 hfe

  set G : Fin r → PowerSeries Lc := fun l => PowerSeries.map ι (taylorSeries v₀ tR (Y l)) with hG
  have hGbd : ∀ l n, ‖PowerSeries.coeff n (G l)‖ * ρ ^ n ≤ 1 := by
    intro l n
    rw [hG]; dsimp only
    rw [PowerSeries.coeff_map, coeff_taylorSeries, hι]
    exact hA l n
  set FL : PowerSeries Lc := PowerSeries.map ι (taylorSeries v₀ tR (u * ((s i)⁻¹) ^ k)) with hFL_def
  have hFL : FL = ∑ φ ∈ Finset.univ, PowerSeries.C (ι (cf φ)) * ∏ j, G (φ j) := by
    rw [hFL_def, hfrep, taylorSeries_sum_smul_prod v₀ (hrat v₀) hUt Y hYmem cf, map_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [map_mul, PowerSeries.map_C, map_prod]
  set M : ℝ := ⨆ φ, μ (cf φ) with hM
  have hMφ : ∀ φ, ‖ι (cf φ)‖ ≤ M := fun φ => by
    rw [hι, hM]; exact le_ciSup (f := fun φ => μ (cf φ)) (Set.finite_range _).bddAbove φ
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMφ (fun _ => i))
  have hFLbd : ∀ n, ‖PowerSeries.coeff n FL‖ * ρ ^ n ≤ M := by
    intro n; rw [hFL]
    exact hGauss (fun φ => ι (cf φ)) (fun φ j => G (φ j)) hρ.le hM0 (fun φ _ j n => hGbd _ n) (fun φ _ => hMφ φ) n

  have hFLvan : ∀ n < e, PowerSeries.coeff n FL = 0 := by
    intro n hn; rw [hFL_def, PowerSeries.coeff_map, coeff_taylorSeries, hvan n hn, map_zero]
  have hFLe : ‖PowerSeries.coeff e FL‖ = μ (v₀.evalAt (u * ((s i)⁻¹) ^ k * tR⁻¹ ^ e)) := by
    rw [hFL_def, PowerSeries.coeff_map, coeff_taylorSeries, hcoefe, hι]
  have hcoefpos : 0 < μ (v₀.evalAt (u * ((s i)⁻¹) ^ k * tR⁻¹ ^ e)) := μ.pos hcoefe0

  set T : Finset (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) := B'.support.filter (fun w => inBall μ s v₀ Λ w) with hT_def
  set a : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Lc := fun w => ι (w.evalAt z - v₀.evalAt z) with ha_def
  have hT : ∀ w ∈ T, w ∈ B'.support ∧ inBall μ s v₀ Λ w := fun w hw => Finset.mem_filter.mp hw
  have hB'v₀ : B' v₀ = 0 := by
    have h1 := hB'le v₀; rw [Finsupp.erase_same] at h1; exact le_antisymm h1 (hB'0 v₀)
  have hTne : ∀ w ∈ T, w ≠ v₀ := by
    intro w hw h; have := (hT w hw).1; rw [h, Finsupp.mem_support_iff] at this; exact this hB'v₀
  have hΔne : ∀ w ∈ T, w.evalAt z - v₀.evalAt z ≠ 0 := fun w hw =>
    sub_ne_zero.mpr (hC w v₀ (hT w hw).2 hball0 (hTne w hw)).1
  have ha0 : ∀ w ∈ T, a w ≠ 0 := fun w hw => by rw [ha_def]; exact (map_ne_zero ι).mpr (hΔne w hw)
  have hanorm : ∀ w, ‖a w‖ = μ (w.evalAt z - v₀.evalAt z) := fun w => hι _
  have hΔpos : ∀ w ∈ T, 0 < μ (w.evalAt z - v₀.evalAt z) := fun w hw => μ.pos (hΔne w hw)
  have halt : ∀ w ∈ T, ‖a w‖ < ρ := by
    intro w hw
    have hprox : Λ < prox μ (evalVec s v₀) (evalVec s w) := (hT w hw).2.resolve_left (hTne w hw)
    have hC2 := (hC v₀ w hball0 (hT w hw).2 (Ne.symm (hTne w hw))).2
    rw [← μ.map_neg, neg_sub] at hC2
    rw [hanorm, ← Real.log_lt_log_iff (hΔpos w hw) hρ, hlogρ]
    linarith
  have hainj : Set.InjOn a T := by
    intro w hw w' hw' h
    by_contra hne
    have h1 := (hC w w' (hT w hw).2 (hT w' hw').2 hne).1
    apply h1
    have h2 : w.evalAt z - v₀.evalAt z = w'.evalAt z - v₀.evalAt z := ι.injective h
    exact sub_left_inj.mp h2

  have horder : ∀ w ∈ T, ((B' w).toNat : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' kk : ℕ, PowerSeries.coeff (n + kk) FL * ((n + kk).choose n : Lc) * (a w) ^ kk).order := by
    intro w hw
    obtain ⟨hUw, hUtw⟩ := hU w (hT w hw).2
    have hYmemw : ∀ l, Y l ∈ w.toValuationSubring := ratio_mem_of_forall_ord_le w s hs0 i hUw
    have hfmemw : u * ((s i)⁻¹) ^ k ∈ w.toValuationSubring := by
      refine P2MW.mem_of_eq_zero_or_ord_nonneg w (Or.inr ?_)
      rw [ord_mul_inv_pow_eq s hs w i hUw hu0 B hB]; exact hBnn w

    have h1 := hShift (fun φ => ι (cf φ)) (fun φ j => G (φ j)) hρ (fun φ _ j n => hGbd _ n) (a w) (halt w hw)
    have h2 : ∀ l, (PowerSeries.mk fun n => ∑' kk : ℕ, PowerSeries.coeff (n + kk) (G l) * ((n + kk).choose n : Lc) * (a w) ^ kk)
        = PowerSeries.map ι (taylorSeries w (chartUnif s i c w) (Y l)) := by
      intro l
      have hb := hBm Lc ι hι w (hT w hw).2 l
      rw [hG]; dsimp only
      rw [taylorSeries, taylorSeries, hb]
    have h3 : (PowerSeries.mk fun n => ∑' kk : ℕ, PowerSeries.coeff (n + kk) FL * ((n + kk).choose n : Lc) * (a w) ^ kk)
        = PowerSeries.map ι (taylorSeries w (chartUnif s i c w) (u * ((s i)⁻¹) ^ k)) := by
      rw [hFL, h1, hfrep, taylorSeries_sum_smul_prod w (hrat w) hUtw Y hYmemw cf, map_sum]
      refine Finset.sum_congr rfl fun φ _ => ?_
      rw [map_mul, PowerSeries.map_C, map_prod]
      congr 1
      exact Finset.prod_congr rfl fun j _ => h2 (φ j)
    rw [h3]
    have hBw : B' w ≤ B w := by have := hB'le w; rwa [Finsupp.erase_ne (hTne w hw)] at this
    have hvanw : ∀ q, q < (B w).toNat → w.taylorCoeff (chartUnif s i c w) q (u * ((s i)⁻¹) ^ k) = 0 :=
      (Place.forall_lt_taylorCoeff_eq_zero_iff_le_ord w (hrat w) hUtw hfmemw hf0 (B w).toNat).mpr
        (by rw [ord_mul_inv_pow_eq s hs w i hUw hu0 B hB, Int.toNat_of_nonneg (hBnn w)])
    have hle : (B' w).toNat ≤ (B w).toNat := Int.toNat_le_toNat hBw
    refine le_trans (by exact_mod_cast hle) (PowerSeries.nat_le_order _ _ fun q hq => ?_)
    rw [PowerSeries.coeff_map, coeff_taylorSeries, hvanw q hq, map_zero]

  set S : Multiset Lc := zerosMultiset T (fun w => (B' w).toNat) a with hS_def
  have hS1 : ∀ x ∈ S, ‖x‖ < ρ := by
    intro x hx; obtain ⟨w, hw, rfl⟩ := exists_of_mem_zerosMultiset T _ a hx; exact halt w hw
  have hS0 : ∀ x ∈ S, x ≠ 0 := by
    intro x hx; obtain ⟨w, hw, rfl⟩ := exists_of_mem_zerosMultiset T _ a hx; exact ha0 w hw
  have hSord : ∀ x ∈ S, (S.count x : ℕ∞)
      ≤ (PowerSeries.mk fun n => ∑' kk : ℕ, PowerSeries.coeff (n + kk) FL * ((n + kk).choose n : Lc) * x ^ kk).order := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := exists_of_mem_zerosMultiset T _ a hx
    rw [hS_def, count_zerosMultiset T _ a hainj hw]
    exact horder w hw
  have hSJ := PowerSeries.norm_coeff_mul_pow_le_mul_prod_of_forall_coeff_eq_zero FL hρ hFLbd e hFLvan S hS1 hS0 hSord
  rw [hS_def, prod_map_zerosMultiset] at hSJ

  have hprodpos : 0 < ∏ w ∈ T, (‖a w‖ / ρ) ^ (B' w).toNat :=
    Finset.prod_pos fun w hw => pow_pos (div_pos (norm_pos_iff.mpr (ha0 w hw)) hρ) _
  have hLHSpos : 0 < ‖PowerSeries.coeff e FL‖ * ρ ^ e := by rw [hFLe]; exact mul_pos hcoefpos (pow_pos hρ e)
  have hMpos : 0 < M := by
    by_contra h
    rw [not_lt] at h
    have := mul_nonpos_of_nonpos_of_nonneg h hprodpos.le
    linarith
  have hlog := Real.log_le_log hLHSpos hSJ
  rw [Real.log_mul (by rw [hFLe]; exact hcoefpos.ne') (pow_ne_zero _ hρ.ne'), Real.log_pow, hFLe, hlogρ,
    Real.log_mul hMpos.ne' hprodpos.ne',
    log_prod_pow_eq_sum T (fun w => (B' w).toNat) (fun w => ‖a w‖ / ρ) (fun w hw => div_pos (norm_pos_iff.mpr (ha0 w hw)) hρ)] at hlog
  have hsum : ∑ w ∈ T, (((B' w).toNat : ℕ) : ℝ) * Real.log (‖a w‖ / ρ)
      = ∑ w ∈ T, (B' w : ℝ) * (Real.log (μ (w.evalAt z - v₀.evalAt z)) + Λ) := by
    refine Finset.sum_congr rfl fun w hw => ?_
    have hcast : (((B' w).toNat : ℕ) : ℝ) = (B' w : ℝ) := by
      have := Int.toNat_of_nonneg (hB'0 w); exact_mod_cast this
    rw [hcast, Real.log_div (norm_pos_iff.mpr (ha0 w hw)).ne' hρ.ne', hanorm, hlogρ, sub_neg_eq_add]
  rw [hsum] at hlog
  linarith

end Core

end P2MJB

end

open AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (S₀ : Finset ℕ) :
    ∃ c₀ : ℝ, ∀ (k : ℕ) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
      (c : (Fin k → Fin r) → ↥L) (u : modularFunctionFieldBar N), u ≠ 0 →
      u = ∑ φ : Fin k → Fin r, ((c φ : ↥L) : AlgebraicClosure ℚ) • ∏ l, s (φ l) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (ν : NumberField.FinitePlace ↥L) (p : ℕ), p.Prime → p ∈ S₀ → ν (p : ↥L) < 1 →
      ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (B' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ w, 0 ≤ B' w) → (∀ w, B' w ≤ (B.erase v₀) w) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B'.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
      ∀ (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
      ∀ a : ↥L, (a : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
      ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        (0 < B v₀ → (⨆ p, ν (y p)) ≠ 0) →
        Real.log (ν a)
          ≤ Real.log (⨆ φ, ν (c φ))
            + ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p))
            - (B'.sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
            + c₀ * k * (-Real.log (ν (p : ↥L))) := by
  classical
  refine P2MJB.jensen_bad_at_le_of_chart N s hs S₀ (fun p hp => ?_) (fun p n₀ hp μ hμ hμp v₀ i hpiv c hspec k cf u hu0 hurep B hB B' hB'0 hB'le => ?_)
  ·
    obtain ⟨n₀, h⟩ := ModularCurve.JZero.exists_chart_of_isPivot N s hs p hp
    refine ⟨n₀, fun μ hμ hμp R i hpiv => ?_⟩
    obtain ⟨c, hc⟩ := h μ hμ hμp R i hpiv
    exact ⟨c, hc⟩
  ·
    haveI : IsUltrametricDist μ.Completion := AbsoluteValue.Completion.isUltrametricDist_of_isNonarchimedean μ hμ
    obtain ⟨hnorm, hnt⟩ := AbsoluteValue.Completion.norm_coe_and_exists_one_lt_norm μ
    have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hμnt : μ.IsNontrivial := ⟨(p : AlgebraicClosure ℚ), hp0, hμp.ne⟩
    letI : NontriviallyNormedField μ.Completion :=
      { (inferInstance : NormedField μ.Completion) with non_trivial := hnt hμnt }
    exact P2MJB.core_coeff_bound s hs p hp n₀ μ v₀ i c hspec cf u hu0 hurep B hB B' hB'0 hB'le μ.Completion
      ((UniformSpace.Completion.coeRingHom).comp (WithAbs.equiv μ).symm.toRingHom) (fun x => hnorm x)
      (fun cc G ρ M hρ hM hF hc n => PowerSeries.norm_coeff_sum_C_mul_prod_mul_pow_le Finset.univ cc G hρ hM hF hc n)
      (fun cc G ρ hρ hF a ha => PowerSeries.taylorShift_sum_C_mul_prod Finset.univ cc G hρ hF a ha)

end S_ModularCurve_JZero_jensen_bad_at_le
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_bad_at_le (solution)
