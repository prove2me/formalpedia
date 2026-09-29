-- Prove2me | solution 1 for ModularCurve.exists_log_absValue_evalAt_ge_of_forall_prox_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/25e0ec34-3c98-57d4-a6af-b81209635410

import Mathlib
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_JZero_chordVec_ne_zero_of_ne
import Theorems.Thm_MvPolynomial_abv_eval_sub_eval_le_mul_iSup
import Theorems.Thm_ModularCurve_JZero_exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_ModularCurve_JZero_exists_abv_evalAt_eq_abv_evalAt_of_le_prox
import Theorems.Thm_ModularCurve_JZero_exists_one_le_abv_evalAt_of_le_prox
import Theorems.Thm_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero
import Theorems.Thm_ModularCurve_JZero_exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_log_absValue_evalAt_ge_of_forall_prox_le
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong"
p2m_attr_erase "simp" "AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.qExpandAlgHomC_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

section P2MPiece0

open AlgebraicCurve

namespace P2MC27

theorem exists_const_forall {ι : Type*} (S : Finset ι) (P : ι → ℝ → Prop)
    (hmono : ∀ i κ κ', κ ≤ κ' → P i κ → P i κ') (h : ∀ i ∈ S, ∃ κ, 0 ≤ κ ∧ P i κ) :
    ∃ κ, 0 ≤ κ ∧ ∀ i ∈ S, P i κ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun i hi => by simp at hi⟩
  | insert a S ha ih =>
    obtain ⟨κ₁, hκ₁, h₁⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    obtain ⟨κ₂, hκ₂, h₂⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨max κ₁ κ₂, le_max_of_le_left hκ₁, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hmono _ _ _ (le_max_right _ _) h₂
    · exact hmono _ _ _ (le_max_left _ _) (h₁ i hi)

section Uniform

local notation "QQ" => AlgebraicClosure ℚ

theorem neg_log_nonneg (μ : AbsoluteValue QQ ℝ) {p : ℕ} (hμp : μ (p : QQ) < 1) :
    0 ≤ -Real.log (μ (p : QQ)) :=
  neg_nonneg.mpr (Real.log_nonpos (μ.nonneg _) hμp.le)

theorem uniform_log_bound (S : Finset QQ) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue QQ ℝ, IsNonarchimedean μ → μ (p : QQ) < 1 →
      ∀ β ∈ S, β ≠ 0 → |Real.log (μ β)| ≤ c * (-Real.log (μ (p : QQ))) := by
  obtain ⟨c, hc0, hc⟩ := exists_const_forall S
    (fun β c => ∀ μ : AbsoluteValue QQ ℝ, IsNonarchimedean μ → μ (p : QQ) < 1 → β ≠ 0 →
      |Real.log (μ β)| ≤ c * (-Real.log (μ (p : QQ))))
    (fun β κ κ' hle hκ μ hμ hμp hβ => (hκ μ hμ hμp hβ).trans
      (mul_le_mul_of_nonneg_right hle (neg_log_nonneg μ hμp)))
    (fun β _ => by
      by_cases hβ : β = 0
      · exact ⟨0, le_rfl, fun μ _ _ h => absurd hβ h⟩
      · obtain ⟨c, hc0, hc⟩ :=
          exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic β hβ ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic β) p hp
        exact ⟨c, hc0, fun μ hμ hμp _ => hc μ hμ hμp⟩)
  exact ⟨c, hc0, fun μ hμ hμp β hβS hβ => hc β hβS μ hμ hμp hβ⟩

end Uniform

section AbsVal

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ)

theorem exp_neg_le_and_le_exp_of_abs_log_le {β : K} (hβ : β ≠ 0) {B : ℝ}
    (h : |Real.log (μ β)| ≤ B) : Real.exp (-B) ≤ μ β ∧ μ β ≤ Real.exp B := by
  have hpos : 0 < μ β := μ.pos hβ
  rw [abs_le] at h
  constructor
  · calc Real.exp (-B) ≤ Real.exp (Real.log (μ β)) := Real.exp_le_exp.mpr h.1
      _ = μ β := Real.exp_log hpos
  · calc μ β = Real.exp (Real.log (μ β)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp B := Real.exp_le_exp.mpr h.2

theorem gaussNorm_le_of_forall_coeff (q : Polynomial K) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ k, q.coeff k ≠ 0 → μ (q.coeff k) ≤ B) : q.gaussNorm μ 1 ≤ B := by
  obtain ⟨k, hk⟩ := Polynomial.exists_eq_gaussNorm μ 1 q
  rw [hk, one_pow, mul_one]
  by_cases h0 : q.coeff k = 0
  · rw [h0, map_zero]; exact hB
  · exact h k h0

theorem abv_coeff_le_gaussNorm (q : Polynomial K) (k : ℕ) : μ (q.coeff k) ≤ q.gaussNorm μ 1 := by
  simpa using Polynomial.le_gaussNorm μ q zero_le_one k

variable {n : ℕ}

theorem exists_abv_max (hn : 0 < n) (x : Fin n → K) : ∃ i, ∀ l, μ (x l) ≤ μ (x i) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image Finset.univ (fun l => μ (x l)) Finset.univ_nonempty
  exact ⟨i, fun l => hi l (Finset.mem_univ l)⟩

theorem renorm_apply_self (x : Fin n → K) (i : Fin n) (hxi : x i ≠ 0) :
    ((x i)⁻¹ • x) i = 1 := by
  rw [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hxi]

theorem abv_renorm_le_one (x : Fin n → K) (i : Fin n) (hxi : x i ≠ 0)
    (hmax : ∀ l, μ (x l) ≤ μ (x i)) (l : Fin n) : μ (((x i)⁻¹ • x) l) ≤ 1 := by
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, inv_mul_le_iff₀ (μ.pos hxi), mul_one]
  exact hmax l

theorem exists_smul_apply_eq_one (hn : 0 < n) (x : Fin n → K) (hx : x ≠ 0) :
    ∃ (c : K) (i : Fin n), c ≠ 0 ∧ (c • x) i = 1 ∧ ∀ l, μ ((c • x) l) ≤ 1 := by
  obtain ⟨i, hi⟩ := exists_abv_max μ hn x
  have hxi : x i ≠ 0 := by
    intro h0
    apply hx
    funext l
    have : μ (x l) ≤ 0 := by simpa [h0] using hi l
    exact (AbsoluteValue.eq_zero μ).mp (le_antisymm this (μ.nonneg _))
  exact ⟨(x i)⁻¹, i, inv_ne_zero hxi, renorm_apply_self x i hxi, abv_renorm_le_one μ x i hxi hi⟩

theorem abv_le_iSup_abv {ι : Type*} [Finite ι] (f : ι → K) (l : ι) : μ (f l) ≤ ⨆ m, μ (f m) :=
  le_ciSup (Finite.bddAbove_range fun m => μ (f m)) l

theorem eq_zero_of_iSup_abv_eq_zero {ι : Type*} [Finite ι] (f : ι → K) (h : (⨆ l, μ (f l)) = 0)
    (l : ι) : f l = 0 := by
  have hle := abv_le_iSup_abv μ f l
  rw [h] at hle
  exact (AbsoluteValue.eq_zero μ).mp (le_antisymm hle (μ.nonneg _))

theorem iSup_abv_ne_zero_of_ne_zero {ι : Type*} [Finite ι] (f : ι → K) {l : ι} (h : f l ≠ 0) :
    (⨆ l, μ (f l)) ≠ 0 := fun h0 => h (eq_zero_of_iSup_abv_eq_zero μ f h0 l)

theorem iSup_abv_pos_of_ne_zero {ι : Type*} [Finite ι] (f : ι → K) {l : ι} (h : f l ≠ 0) :
    0 < ⨆ l, μ (f l) :=
  lt_of_le_of_ne (Real.iSup_nonneg fun _ => μ.nonneg _) (iSup_abv_ne_zero_of_ne_zero μ f h).symm

theorem eq_of_iSup_abv_sub_eq_zero (x y : Fin n → K) (h : (⨆ l, μ (x l - y l)) = 0) : x = y :=
  funext fun l => sub_eq_zero.mp (eq_zero_of_iSup_abv_eq_zero μ (fun l => x l - y l) h l)

theorem minor_smul_eq_zero (x : Fin n → K) (t : K) (p : Fin n × Fin n) :
    x p.1 * (t • x) p.2 - x p.2 * (t • x) p.1 = 0 := by
  simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem iSup_minors_smul_eq_zero (hn : 0 < n) (x : Fin n → K) (t : K) :
    (⨆ p : Fin n × Fin n, μ (x p.1 * (t • x) p.2 - x p.2 * (t • x) p.1)) = 0 := by
  haveI : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  simp_rw [minor_smul_eq_zero, map_zero, ciSup_const]

theorem smul_eq_of_iSup_minors_eq_zero (x a : Fin n → K) (i : Fin n) (hai : a i = 1)
    (h : (⨆ p : Fin n × Fin n, μ (x p.1 * a p.2 - x p.2 * a p.1)) = 0) : (x i) • a = x := by
  funext l
  have h0 := eq_zero_of_iSup_abv_eq_zero μ
    (fun p : Fin n × Fin n => x p.1 * a p.2 - x p.2 * a p.1) h (l, i)
  simp only [hai, mul_one] at h0
  rw [Pi.smul_apply, smul_eq_mul]
  exact (sub_eq_zero.mp h0).symm

theorem smul_eq_of_renorm_eq (x a : Fin n → K) (i : Fin n) (hxi : x i ≠ 0)
    (h : (x i)⁻¹ • x = a) : (x i) • a = x := by
  rw [← h, smul_smul, mul_inv_cancel₀ hxi, one_smul]

theorem iSup_minors_eq_zero_of_smul_eq (hn : 0 < n) (x a y : Fin n → K) (i : Fin n)
    (hxi : x i ≠ 0) (hxa : (x i) • a = x) {e : K} (hy : e • a = y) :
    (⨆ p : Fin n × Fin n, μ (x p.1 * y p.2 - x p.2 * y p.1)) = 0 := by
  have : y = (e * (x i)⁻¹) • x := by
    calc y = e • a := hy.symm
      _ = (e * (x i)⁻¹ * x i) • a := by rw [inv_mul_cancel_right₀ hxi]
      _ = (e * (x i)⁻¹) • ((x i) • a) := by rw [smul_smul]
      _ = (e * (x i)⁻¹) • x := by rw [hxa]
  subst this
  exact iSup_minors_smul_eq_zero μ hn x _

theorem prox_eq_prox_renorm_of_smul_eq (x a y : Fin n → K) (i : Fin n) (hxi : x i ≠ 0)
    {e : K} (he : e ≠ 0) (hy : e • a = y)
    (hg : (⨆ p : Fin n × Fin n, μ (x p.1 * y p.2 - x p.2 * y p.1)) ≠ 0) :
    prox μ x y = prox μ ((x i)⁻¹ • x) a := by
  have key := AlgebraicCurve.prox_smul_smul μ x y (inv_ne_zero hxi) (inv_ne_zero he) hg
  rw [← hy, smul_smul, inv_mul_cancel₀ he, one_smul] at key
  rw [← hy]
  exact key.symm

theorem prox_eq_prox_renorm (x a : Fin n → K) (i : Fin n) (hxi : x i ≠ 0)
    (hg : (⨆ p : Fin n × Fin n, μ (x p.1 * a p.2 - x p.2 * a p.1)) ≠ 0) :
    prox μ x a = prox μ ((x i)⁻¹ • x) a := by
  have key := AlgebraicCurve.prox_smul_smul μ x a (inv_ne_zero hxi) one_ne_zero hg
  rw [one_smul] at key
  exact key.symm

end AbsVal

end P2MC27

end P2MPiece0

section P2MPiece1

open AlgebraicCurve ModularCurve Polynomial

namespace P2MC27

section PlaceGeneric

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_of_evalAt_ne_zero (v : Place K F) {f : F} (h : v.evalAt f ≠ 0) :
    f ∈ v.toValuationSubring := by
  by_contra hf
  apply h
  unfold Place.evalAt
  rw [dif_neg hf]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]

theorem ne_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (h : v.evalAt f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (evalAt_zero v)

theorem residue_ne_zero_of_evalAt_ne_zero (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
  intro h0
  apply h
  rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem isUnit_of_evalAt_ne_zero (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) :=
  (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (residue_ne_zero_of_evalAt_ne_zero v hf h)

theorem ord_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have hf := mem_of_evalAt_ne_zero v h
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero v hf h
  have : f = ((u : v.toValuationSubring) : F) := by rw [hu]
  rw [this]
  exact v.ord_coe_unit u

theorem evalAt_inv_of_evalAt_ne_zero (v : Place K F) (hv : v.IsRational) {f : F} (h : v.evalAt f ≠ 0) :
    f⁻¹ ∈ v.toValuationSubring ∧ v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hf := mem_of_evalAt_ne_zero v h
  have hf0 := ne_zero_of_evalAt_ne_zero v h
  have hord := ord_eq_zero_of_evalAt_ne_zero v h
  have hfi : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf0) (by rw [Place.ord_inv, hord, neg_zero])
  refine ⟨hfi, ?_⟩
  have hmul := v.evalAt_mul_of_mem hv hf hfi
  rw [mul_inv_cancel₀ hf0, v.evalAt_one] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

noncomputable def evalHom (v : Place K F) (hv : v.IsRational) : v.toValuationSubring →+* K where
  toFun f := v.evalAt (f : F)
  map_one' := by rw [OneMemClass.coe_one, v.evalAt_one]
  map_mul' f g := v.evalAt_mul_of_mem hv f.2 g.2
  map_zero' := by rw [ZeroMemClass.coe_zero, evalAt_zero]
  map_add' f g := by
    apply v.algebraMap_residueField_injective
    rw [AddMemClass.coe_add, map_add, v.algebraMap_evalAt hv (add_mem f.2 g.2),
      v.algebraMap_evalAt hv f.2, v.algebraMap_evalAt hv g.2, ← map_add]
    rfl

theorem evalHom_apply (v : Place K F) (hv : v.IsRational) (f : v.toValuationSubring) :
    evalHom v hv f = v.evalAt (f : F) := rfl

theorem evalEval_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) (H : Polynomial (Polynomial K))
    {y w : F} (hy : y ∈ v.toValuationSubring) (hw : w ∈ v.toValuationSubring)
    (h0 : (H.map (mapRingHom (algebraMap K F))).evalEval y w = 0) :
    H.evalEval (v.evalAt y) (v.evalAt w) = 0 := by
  set O := v.toValuationSubring with hO
  let φ : K →+* O := algebraMap K O
  let ι : O →+* F := O.subtype
  let ε : O →+* K := evalHom v hv
  have hιφ : ι.comp φ = algebraMap K F := RingHom.ext fun a => v.coe_algebraMap a
  have hεφ : ε.comp φ = RingHom.id K := RingHom.ext fun a => by
    show v.evalAt ((algebraMap K O a : O) : F) = a
    rw [v.coe_algebraMap, v.evalAt_algebraMap_eq]
  have h1 : H.map (mapRingHom (algebraMap K F)) = (H.map (mapRingHom φ)).map (mapRingHom ι) := by
    rw [Polynomial.map_map, mapRingHom_comp, hιφ]
  have h2 : ι ((H.map (mapRingHom φ)).evalEval ⟨y, hy⟩ ⟨w, hw⟩) = 0 := by
    rw [← map_mapRingHom_evalEval ι, ← h1]
    exact h0
  have h3 : (H.map (mapRingHom φ)).evalEval ⟨y, hy⟩ ⟨w, hw⟩ = 0 := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h2
  have h4 := congrArg ε h3
  rw [map_zero, ← map_mapRingHom_evalEval ε, Polynomial.map_map, mapRingHom_comp, hεφ,
    mapRingHom_id, Polynomial.map_id] at h4
  exact h4

end PlaceGeneric

section Pivot

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem exists_forall_ord_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]
  exact Classical.choose_spec hex j

theorem evalVec_apply (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]
  simp only [dif_pos hr]

theorem evalVec_pivot (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) : evalVec s v (pivotIndex s v hr) = 1 := by
  rw [evalVec_apply hr, mul_inv_cancel₀ (hs _), Place.evalAt_one]

theorem ratio_pivot_mem (hr : 0 < r) (s : Fin r → F) (hs : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    s i * (s (pivotIndex s v hr))⁻¹ ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs i) (inv_ne_zero (hs _)))
    (by rw [v.ord_mul (hs i) (inv_ne_zero (hs _)), v.ord_inv]; linarith [ord_pivot_le hr s v i])

end Pivot

section Bar

variable {N : ℕ} [NeZero N] {r : ℕ}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar N

theorem isRational_bar (v : Place QQ FF) : v.IsRational :=
  (Place.isRational_iff_deg_eq_one v).mpr (deg_eq_one_modularFunctionFieldBar N v)

theorem one_mem_riemannRochSpace_embDivisor :
    (1 : FF) ∈ riemannRochSpace (embDivisor N) := by
  classical
  rw [mem_riemannRochSpace_iff]
  intro v
  right
  rw [Place.ord_one]
  have : 0 ≤ embDivisor N v := by
    rw [ModularCurve.embDivisor, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs <;> simp
  linarith

theorem pos_of_isEmbBasis {s : Fin r → FF} (hs : IsEmbBasis N s) : 0 < r := by
  by_contra hr
  have hr0 : r = 0 := by omega
  subst hr0
  have h1 : (1 : FF) ∈ Submodule.span QQ (Set.range s) :=
    hs.2 ▸ one_mem_riemannRochSpace_embDivisor
  rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at h1
  exact one_ne_zero h1

theorem emb_ne_zero {s : Fin r → FF} (hs : IsEmbBasis N s) (i : Fin r) : s i ≠ 0 :=
  hs.1.ne_zero i

theorem evalVec_ne_zero' {s : Fin r → FF} (hs : IsEmbBasis N s) (R : Place QQ FF) :
    ∃ k, evalVec s R k = 1 :=
  ⟨pivotIndex s R (pos_of_isEmbBasis hs), evalVec_pivot _ s (emb_ne_zero hs) R⟩

theorem renorm_evalVec (hr : 0 < r) {s : Fin r → FF} (hs : IsEmbBasis N s)
    (R : Place QQ FF) (i : Fin r) (hxi : evalVec s R i ≠ 0) (l : Fin r) :
    s l * (s i)⁻¹ ∈ R.toValuationSubring ∧
      (evalVec s R i)⁻¹ * evalVec s R l = R.evalAt (s l * (s i)⁻¹) := by
  have hs0 := emb_ne_zero hs
  have hmi : s i * (s (pivotIndex s R hr))⁻¹ ∈ R.toValuationSubring := ratio_pivot_mem hr s hs0 R i
  have hml : s l * (s (pivotIndex s R hr))⁻¹ ∈ R.toValuationSubring := ratio_pivot_mem hr s hs0 R l
  rw [evalVec_apply hr] at hxi
  have hu0 : s i * (s (pivotIndex s R hr))⁻¹ ≠ 0 := mul_ne_zero (hs0 i) (inv_ne_zero (hs0 _))
  obtain ⟨hinv_mem, hinv⟩ := evalAt_inv_of_evalAt_ne_zero R (isRational_bar R) hxi
  have hprod : s l * (s i)⁻¹
      = (s l * (s (pivotIndex s R hr))⁻¹) * (s i * (s (pivotIndex s R hr))⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv, mul_assoc, mul_comm ((s i)⁻¹), ← mul_assoc, ← mul_assoc,
      inv_mul_cancel_right₀ (hs0 _)]
  constructor
  · rw [hprod]; exact mul_mem hml hinv_mem
  · rw [hprod, R.evalAt_mul_of_mem (isRational_bar R) hml hinv_mem, hinv, evalVec_apply hr,
      evalVec_apply hr, mul_comm]

theorem relation_evalAt (hr : 0 < r) {s : Fin r → FF} (hs : IsEmbBasis N s)
    (R : Place QQ FF) (i : Fin r) (hxi : evalVec s R i ≠ 0) (l : Fin r)
    {h : FF} (hh : h ∈ R.toValuationSubring) (H : Polynomial (Polynomial QQ))
    (hrel : (H.map (mapRingHom (algebraMap QQ FF))).evalEval (s l * (s i)⁻¹) h = 0) :
    H.evalEval ((evalVec s R i)⁻¹ * evalVec s R l) (R.evalAt h) = 0 := by
  obtain ⟨hmem, heq⟩ := renorm_evalVec hr hs R i hxi l
  rw [heq]
  exact evalEval_evalAt_eq_zero R (isRational_bar R) H hmem hh hrel

theorem iSup_minors_evalVec_ne_zero {s : Fin r → FF} (hs : IsEmbBasis N s) (μ : AbsoluteValue QQ ℝ)
    {R Q : Place QQ FF} (hRQ : R ≠ Q) :
    (⨆ p : Fin r × Fin r,
      μ (evalVec s R p.1 * evalVec s Q p.2 - evalVec s R p.2 * evalVec s Q p.1)) ≠ 0 := by
  have h := ModularCurve.JZero.chordVec_ne_zero_of_ne N s hs R Q hRQ
  obtain ⟨p, hp⟩ := Function.ne_iff.mp h
  intro h0
  apply hp
  have hle : μ (evalVec s R p.1 * evalVec s Q p.2 - evalVec s R p.2 * evalVec s Q p.1)
      ≤ ⨆ p : Fin r × Fin r,
          μ (evalVec s R p.1 * evalVec s Q p.2 - evalVec s R p.2 * evalVec s Q p.1) :=
    le_ciSup (Finite.bddAbove_range fun p : Fin r × Fin r =>
      μ (evalVec s R p.1 * evalVec s Q p.2 - evalVec s R p.2 * evalVec s Q p.1)) p
  rw [h0] at hle
  exact (AbsoluteValue.eq_zero μ).mp (le_antisymm hle (μ.nonneg _))

end Bar

end P2MC27

end P2MPiece1

section P2MPiece2

open AlgebraicCurve ModularCurve

namespace P2MC27

section HomogeneousEval

theorem eval_smul_of_isHomogeneous {A : Type*} [CommRing A] {σ : Type*} [Fintype σ]
    {φ : MvPolynomial σ A} {k : ℕ} (hφ : φ.IsHomogeneous k) (t : A) (x : σ → A) :
    MvPolynomial.eval (t • x) φ = t ^ k * MvPolynomial.eval x φ := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = k := by
    have := hφ (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    hdeg]
  ring

theorem aeval_smul_of_isHomogeneous {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {σ : Type*} [Fintype σ] {φ : MvPolynomial σ R} {k : ℕ} (hφ : φ.IsHomogeneous k)
    (t : A) (x : σ → A) :
    MvPolynomial.aeval (t • x) φ = t ^ k * MvPolynomial.aeval x φ := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map,
    MvPolynomial.eval₂_eq_eval_map]
  exact eval_smul_of_isHomogeneous (hφ.map (algebraMap R A)) t x

theorem aeval_mul_of_isHomogeneous {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {σ : Type*} [Fintype σ] {φ : MvPolynomial σ R} {k : ℕ} (hφ : φ.IsHomogeneous k)
    (t : A) (x : σ → A) :
    MvPolynomial.aeval (fun l => t * x l) φ = t ^ k * MvPolynomial.aeval x φ :=
  aeval_smul_of_isHomogeneous hφ t x

end HomogeneousEval

section RowFacts

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {n : ℕ}

theorem ne_zero_of_abv_max_of_ne_zero (x : Fin n → K) (i : Fin n)
    (hmax : ∀ l, μ (x l) ≤ μ (x i)) (hx : x ≠ 0) : x i ≠ 0 := by
  intro h0
  apply hx
  funext l
  have : μ (x l) ≤ 0 := by simpa [h0] using hmax l
  exact (AbsoluteValue.eq_zero μ).mp (le_antisymm this (μ.nonneg _))

theorem iSup_abv_eq_one (x : Fin n → K) (i : Fin n) (hxi : x i = 1) (hx : ∀ l, μ (x l) ≤ 1) :
    (⨆ l, μ (x l)) = 1 := by
  haveI : Nonempty (Fin n) := ⟨i⟩
  apply le_antisymm (ciSup_le hx)
  calc (1 : ℝ) = μ (x i) := by rw [hxi, map_one]
    _ ≤ ⨆ l, μ (x l) := le_ciSup (Finite.bddAbove_range fun l => μ (x l)) i

theorem prox_eq_neg_log_iSup_minors (x v : Fin n → K) (i j : Fin n) (hxi : x i = 1) (hvj : v j = 1)
    (hx : ∀ l, μ (x l) ≤ 1) (hv : ∀ l, μ (v l) ≤ 1) :
    prox μ x v = -Real.log (⨆ q : Fin n × Fin n, μ (x q.1 * v q.2 - x q.2 * v q.1)) := by
  rw [prox, iSup_abv_eq_one μ x i hxi hx, iSup_abv_eq_one μ v j hvj hv, Real.log_one]
  ring

theorem iSup_minors_comm (x v : Fin n → K) :
    (⨆ q : Fin n × Fin n, μ (v q.1 * x q.2 - v q.2 * x q.1))
      = ⨆ q : Fin n × Fin n, μ (x q.1 * v q.2 - x q.2 * v q.1) := by
  congr 1
  funext q
  rw [← μ.map_neg]
  congr 1
  ring

end RowFacts

section Zero

variable {N : ℕ} [NeZero N] {r : ℕ}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar N

theorem eval_evalVec_eq_zero_of_aeval_eq_zero (hr : 0 < r) {s : Fin r → FF} (hs : IsEmbBasis N s)
    (R : Place QQ FF) {k : ℕ} (Φ : MvPolynomial (Fin r) QQ) (hΦ : Φ.IsHomogeneous k)
    (h0 : MvPolynomial.aeval s Φ = 0) : MvPolynomial.eval (evalVec s R) Φ = 0 := by
  set O := R.toValuationSubring with hO
  have hs0 := emb_ne_zero hs
  let y : Fin r → O := fun l => ⟨s l * (s (pivotIndex s R hr))⁻¹, ratio_pivot_mem hr s hs0 R l⟩
  let ι : O →+* FF := O.subtype
  let ε : O →+* QQ := evalHom R (isRational_bar R)
  have hιφ : ι.comp (algebraMap QQ O) = algebraMap QQ FF := RingHom.ext fun a => R.coe_algebraMap a
  have hεφ : ε.comp (algebraMap QQ O) = RingHom.id QQ := RingHom.ext fun a => by
    show R.evalAt ((algebraMap QQ O a : O) : FF) = a
    rw [R.coe_algebraMap, R.evalAt_algebraMap_eq]

  have h1 : ι (MvPolynomial.aeval y Φ) = 0 := by
    rw [MvPolynomial.map_aeval, hιφ]
    have hy : (fun l => ι (y l)) = fun l => (s (pivotIndex s R hr))⁻¹ * s l := by
      funext l
      show s l * (s (pivotIndex s R hr))⁻¹ = (s (pivotIndex s R hr))⁻¹ * s l
      rw [mul_comm]
    rw [hy, ← MvPolynomial.aeval_eq_eval₂Hom,
      aeval_mul_of_isHomogeneous hΦ ((s (pivotIndex s R hr))⁻¹) s, h0, mul_zero]
  have h2 : MvPolynomial.aeval y Φ = 0 := by
    apply Subtype.ext
    rw [ZeroMemClass.coe_zero]
    exact h1
  have h3 := congrArg ε h2
  rw [map_zero, MvPolynomial.map_aeval, hεφ] at h3
  have hx : (fun l => ε (y l)) = evalVec s R := by
    funext l
    rw [evalVec_apply hr]
    rfl
  rw [hx] at h3
  exact h3

end Zero

section C25Cor

variable {N : ℕ} [NeZero N] {r : ℕ}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar N

theorem C25_prox_le_of_forall_ne (s : Fin r → FF) (hs : IsEmbBasis N s)
    (v : Fin r → QQ) (hv0 : v ≠ 0)
    (hv : ∀ Q : Place QQ FF, ∀ c : QQ, c • v ≠ evalVec s Q) (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : AbsoluteValue QQ ℝ, IsNonarchimedean μ → μ (p : QQ) < 1 →
      ∀ R : Place QQ FF, prox μ (evalVec s R) v ≤ c * (-Real.log (μ (p : QQ))) := by
  classical
  have hr : 0 < r := pos_of_isEmbBasis hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hv' : ∀ (Q : Place QQ FF) (c : QQ), v ≠ c • evalVec s Q := by
    intro Q c hvc
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hvc
      exact hv0 hvc
    exact hv Q c⁻¹ (by rw [hvc, smul_smul, inv_mul_cancel₀ hc, one_smul])
  obtain ⟨k, Φ, hΦ, hΦs, hΦv⟩ := ModularCurve.JZero.exists_isHomogeneous_aeval_eq_zero_and_eval_ne_zero N s hs v hv'

  set S : Finset QQ := (Φ.support.image fun m => Φ.coeff m) ∪ (Finset.univ.image v)
    ∪ {MvPolynomial.eval v Φ} with hSdef
  have hScoef : ∀ m, Φ.coeff m ≠ 0 → Φ.coeff m ∈ S := fun m hm => by
    rw [hSdef]
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩))
  have hSv : ∀ l, v l ∈ S := fun l => by
    rw [hSdef]
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩))
  have hSΦ : MvPolynomial.eval v Φ ∈ S := by
    rw [hSdef]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  obtain ⟨c, hc0, hc⟩ := uniform_log_bound S p hp
  refine ⟨((k : ℝ) + 2) * c, by positivity, fun μ hμ hμp R => ?_⟩
  set T := -Real.log (μ (p : QQ)) with hTdef
  have hT : 0 ≤ T := neg_log_nonneg μ hμp
  have hcT : 0 ≤ c * T := mul_nonneg hc0 hT
  have hkcT : 0 ≤ (k : ℝ) * (c * T) := by positivity
  set x := evalVec s R with hxdef

  have hΦx : MvPolynomial.eval x Φ = 0 := eval_evalVec_eq_zero_of_aeval_eq_zero hr hs R Φ hΦ hΦs

  have hk₀ : x (pivotIndex s R hr) = 1 := evalVec_pivot hr s (emb_ne_zero hs) R
  have hg : (⨆ q : Fin r × Fin r, μ (x q.1 * v q.2 - x q.2 * v q.1)) ≠ 0 := by
    intro h0
    have hvx := smul_eq_of_iSup_minors_eq_zero μ v x (pivotIndex s R hr) hk₀
      (by rw [iSup_minors_comm]; exact h0)
    have ht : v (pivotIndex s R hr) ≠ 0 := by
      intro ht0
      apply hv0
      rw [← hvx, ht0, zero_smul]
    apply hv R (v (pivotIndex s R hr))⁻¹
    exact (calc (v (pivotIndex s R hr))⁻¹ • v
          = (v (pivotIndex s R hr))⁻¹ • ((v (pivotIndex s R hr)) • x) := by rw [hvx]
      _ = x := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul])

  obtain ⟨i, hmaxx⟩ := exists_abv_max μ hr x
  obtain ⟨j, hmaxv⟩ := exists_abv_max μ hr v
  have hx0 : x ≠ 0 := fun h0 => by
    have := congrFun h0 (pivotIndex s R hr)
    rw [hk₀, Pi.zero_apply] at this
    exact one_ne_zero this
  have hxi : x i ≠ 0 := ne_zero_of_abv_max_of_ne_zero μ x i hmaxx hx0
  have hvj : v j ≠ 0 := ne_zero_of_abv_max_of_ne_zero μ v j hmaxv hv0
  set xh : Fin r → QQ := (x i)⁻¹ • x with hxhdef
  set vh : Fin r → QQ := (v j)⁻¹ • v with hvhdef
  have hxh1 : xh i = 1 := renorm_apply_self x i hxi
  have hvh1 : vh j = 1 := renorm_apply_self v j hvj
  have hxh_le : ∀ l, μ (xh l) ≤ 1 := abv_renorm_le_one μ x i hxi hmaxx
  have hvh_le : ∀ l, μ (vh l) ≤ 1 := abv_renorm_le_one μ v j hvj hmaxv
  have hprox : prox μ x v = prox μ xh vh :=
    (AlgebraicCurve.prox_smul_smul μ x v (inv_ne_zero hxi) (inv_ne_zero hvj) hg).symm
  set G := ⨆ q : Fin r × Fin r, μ (xh q.1 * vh q.2 - xh q.2 * vh q.1) with hGdef
  have hproxG : prox μ xh vh = -Real.log G :=
    prox_eq_neg_log_iSup_minors μ xh vh i j hxh1 hvh1 hxh_le hvh_le
  rw [hprox, hproxG]
  have hG0 : 0 ≤ G := Real.iSup_nonneg fun q => μ.nonneg _
  by_cases hG1 : 1 ≤ G
  · have := Real.log_nonneg hG1
    have : 0 ≤ ((k : ℝ) + 2) * c * T := by positivity
    linarith
  push Not at hG1
  have hminor_le : ∀ q : Fin r × Fin r, μ (xh q.1 * vh q.2 - xh q.2 * vh q.1) ≤ G := fun q =>
    le_ciSup (Finite.bddAbove_range fun q : Fin r × Fin r =>
      μ (xh q.1 * vh q.2 - xh q.2 * vh q.1)) q

  have hprod1 : μ (xh j * vh i) = 1 := by
    have hlt : μ (1 - xh j * vh i) < 1 := by
      have := hminor_le (i, j)
      simp only [hxh1, hvh1, mul_one] at this
      exact lt_of_le_of_lt this hG1
    have hle : μ (xh j * vh i) ≤ 1 := by
      rw [map_mul]
      exact mul_le_one₀ (hxh_le j) (μ.nonneg _) (hvh_le i)
    have hultra := hμ (1 - xh j * vh i) (xh j * vh i)
    rw [sub_add_cancel, map_one] at hultra
    rcases le_max_iff.mp hultra with h | h
    · exact absurd h (not_le.mpr hlt)
    · exact le_antisymm hle h
  have hxhj : μ (xh j) = 1 := by
    rw [map_mul] at hprod1
    have h1 : μ (xh j) * μ (vh i) ≤ μ (xh j) := mul_le_of_le_one_right (μ.nonneg _) (hvh_le i)
    rw [hprod1] at h1
    exact le_antisymm (hxh_le j) h1

  set w : Fin r → QQ := (xh j) • vh with hwdef
  have hw_le : ∀ l, μ (w l) ≤ 1 := fun l => by
    rw [hwdef, Pi.smul_apply, smul_eq_mul, map_mul, hxhj, one_mul]
    exact hvh_le l
  have hdist : (⨆ l, μ (w l - xh l)) ≤ G := by
    refine Real.iSup_le (fun l => ?_) hG0
    have := hminor_le (l, j)
    simp only [hvh1, mul_one] at this
    have hwl : w l - xh l = -(xh l - xh j * vh l) := by
      rw [hwdef, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hwl, μ.map_neg]
    exact this

  have hCΦ : ∀ m, μ (Φ.coeff m) ≤ Real.exp (c * T) := fun m => by
    by_cases hm : Φ.coeff m = 0
    · rw [hm, map_zero]; exact (Real.exp_pos _).le
    · exact (exp_neg_le_and_le_exp_of_abs_log_le μ hm (hc μ hμ hμp _ (hScoef m hm) hm)).2
  have hLip := MvPolynomial.abv_eval_sub_eval_le_mul_iSup μ hμ Φ (Real.exp (c * T)) hCΦ w xh hw_le hxh_le
  have hevxh : MvPolynomial.eval xh Φ = 0 := by
    rw [hxhdef, eval_smul_of_isHomogeneous hΦ, hΦx, mul_zero]
  have hevw : MvPolynomial.eval w Φ = xh j ^ k * ((v j)⁻¹ ^ k * MvPolynomial.eval v Φ) := by
    rw [hwdef, eval_smul_of_isHomogeneous hΦ, hvhdef, eval_smul_of_isHomogeneous hΦ]
  rw [hevxh, sub_zero, hevw, map_mul, map_mul, map_pow, map_pow, hxhj, one_pow, one_mul,
    map_inv₀] at hLip
  have hmain : (μ (v j))⁻¹ ^ k * μ (MvPolynomial.eval v Φ) ≤ Real.exp (c * T) * G :=
    hLip.trans (mul_le_mul_of_nonneg_left hdist (Real.exp_pos _).le)
  have hb1 : μ (v j) ≤ Real.exp (c * T) :=
    (exp_neg_le_and_le_exp_of_abs_log_le μ hvj (hc μ hμ hμp _ (hSv j) hvj)).2
  have hb2 : Real.exp (-(c * T)) ≤ μ (MvPolynomial.eval v Φ) :=
    (exp_neg_le_and_le_exp_of_abs_log_le μ hΦv (hc μ hμ hμp _ hSΦ hΦv)).1
  have hvjpos : 0 < μ (v j) := μ.pos hvj
  have hΦvpos : 0 < μ (MvPolynomial.eval v Φ) := μ.pos hΦv
  have hLHSpos : 0 < (μ (v j))⁻¹ ^ k * μ (MvPolynomial.eval v Φ) :=
    mul_pos (pow_pos (inv_pos.mpr hvjpos) _) hΦvpos
  have hGpos : 0 < G := (mul_pos_iff_of_pos_left (Real.exp_pos (c * T))).mp (hLHSpos.trans_le hmain)
  have hlog := Real.log_le_log hLHSpos hmain
  rw [Real.log_mul (pow_pos (inv_pos.mpr hvjpos) _).ne' hΦvpos.ne', Real.log_pow, Real.log_inv,
    Real.log_mul (Real.exp_pos _).ne' hGpos.ne', Real.log_exp] at hlog
  have hl1 : Real.log (μ (v j)) ≤ c * T := by
    have := Real.log_le_log hvjpos hb1
    rwa [Real.log_exp] at this
  have hl2 : -(c * T) ≤ Real.log (μ (MvPolynomial.eval v Φ)) := by
    have := Real.log_le_log (Real.exp_pos _) hb2
    rwa [Real.log_exp] at this
  have hl3 : (k : ℝ) * Real.log (μ (v j)) ≤ (k : ℝ) * (c * T) :=
    mul_le_mul_of_nonneg_left hl1 (Nat.cast_nonneg k)
  linarith

end C25Cor

end P2MC27

end P2MPiece2

section P2MPiece3

open AlgebraicCurve ModularCurve Polynomial

namespace P2MC27

section GenericBits

variable {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) {n : ℕ}

theorem iSup_pos_of_smul_ne (x a : Fin n → K) (i : Fin n) (hxi : x i ≠ 0) (hne : (x i) • a ≠ x) :
    0 < ⨆ l, μ (((x i)⁻¹ • x) l - a l) := by
  rcases (Real.iSup_nonneg fun l => μ.nonneg (((x i)⁻¹ • x) l - a l)).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (smul_eq_of_renorm_eq x a i hxi (eq_of_iSup_abv_sub_eq_zero μ _ a heq.symm)) hne

end GenericBits

section Candidate

variable {N : ℕ} [NeZero N] {r : ℕ}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar N

theorem ne_zero_of_smul_eq_evalVec {s : Fin r → FF} (hs : IsEmbBasis N s) {a : Fin r → QQ}
    {Q : Place QQ FF} {e : QQ} (he : e • a = evalVec s Q) : e ≠ 0 := by
  rintro rfl
  obtain ⟨k, hk⟩ := evalVec_ne_zero' hs Q
  have := congrFun he k
  rw [zero_smul, Pi.zero_apply, hk] at this
  exact zero_ne_one this

theorem prox_evalVec_eq_neg_log (hr : 0 < r) {s : Fin r → FF} (hs : IsEmbBasis N s)
    (μ : AbsoluteValue QQ ℝ) (hμ : IsNonarchimedean μ) (R Q : Place QQ FF) (hRQ : R ≠ Q)
    (i : Fin r) (hxi : evalVec s R i ≠ 0) (hmax : ∀ l, μ (evalVec s R l) ≤ μ (evalVec s R i))
    (a : Fin r → QQ) (hai : a i = 1) (ha : ∀ l, μ (a l) ≤ 1) {e : QQ} (he : e • a = evalVec s Q) :
    0 < (⨆ l, μ (((evalVec s R i)⁻¹ • evalVec s R) l - a l)) ∧
      prox μ (evalVec s R) (evalVec s Q)
        = -Real.log (⨆ l, μ (((evalVec s R i)⁻¹ • evalVec s R) l - a l)) := by
  have hg := iSup_minors_evalVec_ne_zero hs μ hRQ
  have he0 := ne_zero_of_smul_eq_evalVec hs he
  have hne : (evalVec s R i) • a ≠ evalVec s R := fun hxa =>
    hg (iSup_minors_eq_zero_of_smul_eq μ hr (evalVec s R) a (evalVec s Q) i hxi hxa he)
  refine ⟨iSup_pos_of_smul_ne μ _ a i hxi hne, ?_⟩
  rw [prox_eq_prox_renorm_of_smul_eq μ (evalVec s R) a (evalVec s Q) i hxi he0 he hg]
  exact AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ _ a i
    (renorm_apply_self _ i hxi) hai (abv_renorm_le_one μ _ i hxi hmax) ha

theorem candidate_const (hr : 0 < r) (s : Fin r → FF) (hs : IsEmbBasis N s) (h : FF) (hh : h ≠ 0)
    (p : ℕ) (hp : p.Prime) (i : Fin r) (a : Fin r → QQ) (hai : a i = 1) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ μ : AbsoluteValue QQ ℝ, IsNonarchimedean μ → μ (p : QQ) < 1 →
      ∀ (R : Place QQ FF) (L : ℝ), R.ord h = 0 →
        (∀ Q : Place QQ FF, 0 < Q.ord h → prox μ (evalVec s R) (evalVec s Q) ≤ L) →
        evalVec s R i ≠ 0 → (∀ l, μ (evalVec s R l) ≤ μ (evalVec s R i)) → (∀ l, μ (a l) ≤ 1) →
        ((0 < ⨆ l, μ (((evalVec s R i)⁻¹ • evalVec s R) l - a l)) ∧
            -Real.log (⨆ l, μ (((evalVec s R i)⁻¹ • evalVec s R) l - a l)) ≤ L) ∨
        ((0 < ⨆ l, μ (((evalVec s R i)⁻¹ • evalVec s R) l - a l)) ∧
            -(κ * (-Real.log (μ (p : QQ))))
              ≤ Real.log (⨆ l, μ (((evalVec s R i)⁻¹ • evalVec s R) l - a l))) ∨
        -(κ * (-Real.log (μ (p : QQ)))) ≤ Real.log (μ (R.evalAt h)) ∨
        1 ≤ μ (R.evalAt h) := by
  classical
  by_cases hα : ∃ Q : Place QQ FF, 0 < Q.ord h ∧ ∃ e : QQ, e • a = evalVec s Q
  ·
    obtain ⟨Q, hQ, e, he⟩ := hα
    refine ⟨0, le_rfl, fun μ hμ hμp R L hR hzero hxi hmax ha => Or.inl ?_⟩
    have hRQ : R ≠ Q := by
      rintro rfl
      rw [hR] at hQ
      exact lt_irrefl _ hQ
    obtain ⟨hD, hprox⟩ := prox_evalVec_eq_neg_log hr hs μ hμ R Q hRQ i hxi hmax a hai ha he
    exact ⟨hD, hprox ▸ hzero Q hQ⟩
  · by_cases hβ : ∃ Q : Place QQ FF, ∃ e : QQ, e • a = evalVec s Q
    · obtain ⟨Q', e, he⟩ := hβ
      have hQ'le : Q'.ord h ≤ 0 := not_lt.mp fun hpos => hα ⟨Q', hpos, e, he⟩
      rcases hQ'le.lt_or_eq with hneg | hzeroOrd
      ·
        obtain ⟨κ, hκ0, hκ⟩ := ModularCurve.JZero.exists_one_le_abv_evalAt_of_le_prox N s hs h Q' hneg p hp
        refine ⟨κ, hκ0, fun μ hμ hμp R L hR hzero hxi hmax ha => ?_⟩
        by_cases hfar : κ * (-Real.log (μ (p : QQ))) ≤ prox μ (evalVec s R) (evalVec s Q')
        · exact Or.inr (Or.inr (Or.inr (hκ μ hμ hμp R hR hfar)))
        · have hRQ : R ≠ Q' := by
            rintro rfl
            rw [hR] at hneg
            exact lt_irrefl _ hneg
          obtain ⟨hD, hprox⟩ := prox_evalVec_eq_neg_log hr hs μ hμ R Q' hRQ i hxi hmax a hai ha he
          refine Or.inr (Or.inl ⟨hD, ?_⟩)
          rw [hprox] at hfar
          linarith [not_le.mp hfar]
      ·
        obtain ⟨κ₁, hκ₁0, hκ₁⟩ := ModularCurve.JZero.exists_abv_evalAt_eq_abv_evalAt_of_le_prox N s hs h Q' hzeroOrd p hp
        have hval : Q'.evalAt h ≠ 0 :=
          Q'.evalAt_ne_zero_of_ord_eq_zero (isRational_bar Q') hh hzeroOrd
        obtain ⟨κ₂, hκ₂0, hκ₂⟩ :=
          exists_abs_log_abv_le_mul_neg_log_of_isAlgebraic (Q'.evalAt h) hval ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic _) p hp
        refine ⟨κ₁ + κ₂, add_nonneg hκ₁0 hκ₂0, fun μ hμ hμp R L hR hzero hxi hmax ha => ?_⟩
        have hT := neg_log_nonneg μ hμp
        have hlow : -(κ₂ * (-Real.log (μ (p : QQ)))) ≤ Real.log (μ (Q'.evalAt h)) := by
          have := hκ₂ μ hμ hμp
          rw [abs_le] at this
          exact this.1
        have hk1 : 0 ≤ κ₁ * (-Real.log (μ (p : QQ))) := mul_nonneg hκ₁0 hT
        by_cases hRQ : R = Q'
        · subst hRQ
          refine Or.inr (Or.inr (Or.inl ?_))
          linarith
        by_cases hfar : κ₁ * (-Real.log (μ (p : QQ))) ≤ prox μ (evalVec s R) (evalVec s Q')
        · have heq := hκ₁ μ hμ hμp R hR hfar
          refine Or.inr (Or.inr (Or.inl ?_))
          rw [heq]
          linarith
        · obtain ⟨hD, hprox⟩ := prox_evalVec_eq_neg_log hr hs μ hμ R Q' hRQ i hxi hmax a hai ha he
          refine Or.inr (Or.inl ⟨hD, ?_⟩)
          rw [hprox] at hfar
          have hk2 : 0 ≤ κ₂ * (-Real.log (μ (p : QQ))) := mul_nonneg hκ₂0 hT
          linarith [not_le.mp hfar]
    ·
      have ha0 : a ≠ 0 := fun h0 => by
        have := congrFun h0 i
        rw [hai, Pi.zero_apply] at this
        exact one_ne_zero this
      have hv : ∀ (Q : Place QQ FF) (e : QQ), e • a ≠ evalVec s Q := fun Q e he => hβ ⟨Q, e, he⟩
      obtain ⟨κ, hκ0, hκ⟩ := C25_prox_le_of_forall_ne s hs a ha0 hv p hp
      refine ⟨κ, hκ0, fun μ hμ hμp R L hR hzero hxi hmax ha => ?_⟩
      have hg : (⨆ q : Fin r × Fin r,
          μ (evalVec s R q.1 * a q.2 - evalVec s R q.2 * a q.1)) ≠ 0 := fun h0 =>
        hv R (evalVec s R i) (smul_eq_of_iSup_minors_eq_zero μ (evalVec s R) a i hai h0)
      have hne : (evalVec s R i) • a ≠ evalVec s R := hv R (evalVec s R i)
      have hD := iSup_pos_of_smul_ne μ (evalVec s R) a i hxi hne
      refine Or.inr (Or.inl ⟨hD, ?_⟩)
      have key := hκ μ hμ hμp R
      rw [prox_eq_prox_renorm μ (evalVec s R) a i hxi hg,
        AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ _ a i
          (renorm_apply_self _ i hxi) hai (abv_renorm_le_one μ _ i hxi hmax) ha] at key
      linarith

end Candidate

end P2MC27

end P2MPiece3

section P2MPiece4

open AlgebraicCurve ModularCurve Polynomial

namespace P2MC27

section Main

variable {N : ℕ} [NeZero N] {r : ℕ}

local notation "QQ" => AlgebraicClosure ℚ
local notation "FF" => modularFunctionFieldBar N

theorem C2_main (s : Fin r → FF) (hs : IsEmbBasis N s) (h : FF) (hh : h ≠ 0)
    (p : ℕ) (hp : p.Prime) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 < M ∧ ∀ μ : AbsoluteValue QQ ℝ, IsNonarchimedean μ → μ (p : QQ) < 1 →
      ∀ (R : Place QQ FF) (L : ℝ), 0 ≤ L →
        (∀ Q : Place QQ FF, 0 < Q.ord h → prox μ (evalVec s R) (evalVec s Q) ≤ L) →
        -(C * (-Real.log (μ (p : QQ)))) - M * L ≤ min 0 (Real.log (μ (R.evalAt h))) := by
  classical
  have hr : 0 < r := pos_of_isEmbBasis hs
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩

  choose Hf hHne hP0 hrel using fun i l : Fin r =>
    ModularCurve.JZero.exists_ne_zero_eval_zero_ne_zero_evalEval_div_eq_zero N s hs h hh i l

  set S : Finset QQ := Finset.univ.biUnion fun il : Fin r × Fin r =>
    (Hf il.1 il.2).support.biUnion fun j => ((Hf il.1 il.2).coeff j).support.image
      fun k => ((Hf il.1 il.2).coeff j).coeff k with hSdef
  have hS : ∀ i l j k, ((Hf i l).coeff j).coeff k ≠ 0 → ((Hf i l).coeff j).coeff k ∈ S := by
    intro i l j k hk
    rw [hSdef]
    apply Finset.mem_biUnion.mpr
    refine ⟨(i, l), Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Polynomial.mem_support_iff.mpr ?_, ?_⟩
    · intro hj; apply hk; rw [hj, Polynomial.coeff_zero]
    · exact Finset.mem_image.mpr ⟨k, Polynomial.mem_support_iff.mpr hk, rfl⟩
  obtain ⟨c, hc0, hc⟩ := uniform_log_bound S p hp

  set d : ℕ := Finset.univ.sup fun il : Fin r × Fin r => ((Hf il.1 il.2).eval 0).natDegree
    with hddef
  have hd : ∀ i l, ((Hf i l).eval 0).natDegree ≤ d := fun i l => by
    rw [hddef]
    exact Finset.le_sup (f := fun il : Fin r × Fin r => ((Hf il.1 il.2).eval 0).natDegree)
      (Finset.mem_univ (i, l))

  set cand : Fin r → Finset (Fin r → QQ) := fun i =>
    Fintype.piFinset fun l =>
      if l = i then ({1} : Finset QQ) else ((Hf i l).eval 0).roots.toFinset with hcanddef

  obtain ⟨κ, hκ0, hκ⟩ := exists_const_forall (Finset.univ.sigma cand)
    (fun ia κ => ∀ μ : AbsoluteValue QQ ℝ, IsNonarchimedean μ → μ (p : QQ) < 1 →
      ∀ (R : Place QQ FF) (L : ℝ), R.ord h = 0 →
        (∀ Q : Place QQ FF, 0 < Q.ord h → prox μ (evalVec s R) (evalVec s Q) ≤ L) →
        evalVec s R ia.1 ≠ 0 → (∀ l, μ (evalVec s R l) ≤ μ (evalVec s R ia.1)) →
        (∀ l, μ (ia.2 l) ≤ 1) →
        ((0 < ⨆ l, μ (((evalVec s R ia.1)⁻¹ • evalVec s R) l - ia.2 l)) ∧
            -Real.log (⨆ l, μ (((evalVec s R ia.1)⁻¹ • evalVec s R) l - ia.2 l)) ≤ L) ∨
        ((0 < ⨆ l, μ (((evalVec s R ia.1)⁻¹ • evalVec s R) l - ia.2 l)) ∧
            -(κ * (-Real.log (μ (p : QQ))))
              ≤ Real.log (⨆ l, μ (((evalVec s R ia.1)⁻¹ • evalVec s R) l - ia.2 l))) ∨
        -(κ * (-Real.log (μ (p : QQ)))) ≤ Real.log (μ (R.evalAt h)) ∨
        1 ≤ μ (R.evalAt h))
    (by
      intro ia κ κ' hle H μ hμ hμp R L hR hz hxi hmax ha
      have hT := neg_log_nonneg μ hμp
      have hmul : κ * (-Real.log (μ (p : QQ))) ≤ κ' * (-Real.log (μ (p : QQ))) :=
        mul_le_mul_of_nonneg_right hle hT
      rcases H μ hμ hμp R L hR hz hxi hmax ha with h1 | ⟨hD, h2⟩ | h3 | h4
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨hD, by linarith⟩)
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inr (Or.inr h4)))
    (by
      rintro ⟨i, a⟩ hia
      have hai : a i = 1 := by
        have := (Fintype.mem_piFinset.mp (Finset.mem_sigma.mp hia).2) i
        simpa using this
      exact candidate_const hr s hs h hh p hp i a hai)

  refine ⟨2 * c + (d : ℝ) * κ + κ, (d : ℝ) + 1, by positivity, by positivity, ?_⟩
  intro μ hμ hμp R L hL hzero
  set T := -Real.log (μ (p : QQ)) with hTdef
  have hT : 0 ≤ T := neg_log_nonneg μ hμp
  have hcT : 0 ≤ c * T := mul_nonneg hc0 hT
  have hκT : 0 ≤ κ * T := mul_nonneg hκ0 hT
  have hdκT : 0 ≤ (d : ℝ) * κ * T := by positivity
  have hdL : 0 ≤ (d : ℝ) * L := by positivity

  by_cases hw0 : R.evalAt h = 0
  · rw [hw0, map_zero, Real.log_zero, min_self]
    linarith
  set η := μ (R.evalAt h) with hηdef
  have hη0 : 0 < η := μ.pos hw0

  by_cases hη1 : 1 ≤ η
  · rw [min_eq_left (Real.log_nonneg hη1)]
    linarith
  push Not at hη1
  have hlogη : Real.log η < 0 := Real.log_neg hη0 hη1
  rw [min_eq_right hlogη.le]

  have hmem : h ∈ R.toValuationSubring := mem_of_evalAt_ne_zero R hw0
  have hord : R.ord h = 0 := ord_eq_zero_of_evalAt_ne_zero R hw0

  set x := evalVec s R with hxdef
  obtain ⟨i, hmax⟩ := exists_abv_max μ hr x
  have hxi : x i ≠ 0 := by
    intro h0
    have hpiv : x (pivotIndex s R hr) = 1 := evalVec_pivot hr s (emb_ne_zero hs) R
    have h1 : μ (x (pivotIndex s R hr)) ≤ μ (x i) := hmax _
    rw [hpiv, h0, map_one, map_zero] at h1
    exact absurd h1 (by norm_num)
  set xh : Fin r → QQ := (x i)⁻¹ • x with hxhdef
  have hxh_le : ∀ l, μ (xh l) ≤ 1 := abv_renorm_le_one μ x i hxi hmax
  have hxhi : xh i = 1 := renorm_apply_self x i hxi

  set B := Real.exp (c * T) with hBdef
  have hBpos : 0 < B := Real.exp_pos _
  have hcoef : ∀ i l j, ((Hf i l).coeff j).gaussNorm μ 1 ≤ B := by
    intro i l j
    refine gaussNorm_le_of_forall_coeff μ _ hBpos.le fun k hk => ?_
    exact (exp_neg_le_and_le_exp_of_abs_log_le μ hk (hc μ hμ hμp _ (hS i l j k hk) hk)).2
  have hPlow : ∀ i l, Real.exp (-(c * T)) ≤ ((Hf i l).eval 0).gaussNorm μ 1 := by
    intro i l
    have hP := hP0 i l
    rw [← Polynomial.coeff_zero_eq_eval_zero] at hP ⊢
    obtain ⟨k, hk⟩ : ∃ k, ((Hf i l).coeff 0).coeff k ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hP (Polynomial.ext fun k => by rw [hall k, Polynomial.coeff_zero])
    exact (exp_neg_le_and_le_exp_of_abs_log_le μ hk (hc μ hμ hμp _ (hS i l 0 k hk) hk)).1.trans
      (abv_coeff_le_gaussNorm μ _ k)

  by_cases hsmall : ∀ l, l ≠ i → B * η < ((Hf i l).eval 0).gaussNorm μ 1
  swap
  ·
    push Not at hsmall
    obtain ⟨l, -, hle⟩ := hsmall
    have h1 : Real.exp (-(c * T)) ≤ B * η := (hPlow i l).trans hle
    have h2 : -(c * T) ≤ c * T + Real.log η := by
      have := Real.log_le_log (Real.exp_pos _) h1
      rwa [Real.log_exp, Real.log_mul hBpos.ne' hη0.ne', Real.log_exp] at this
    linarith

  have hroot : ∀ l, l ≠ i → ∃ al ∈ ((Hf i l).eval 0).roots, μ al ≤ 1 ∧
      ((Hf i l).eval 0).gaussNorm μ 1 * μ (xh l - al) ^ ((Hf i l).eval 0).natDegree ≤ B * η := by
    intro l hli
    exact Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero μ hμ
      (Hf i l) (hcoef i l) (hxh_le l)
      (relation_evalAt hr hs R i hxi l hmem (Hf i l) (hrel i l)) (hsmall l hli)
  choose! af haf_mem haf_le haf_bd using hroot

  set a : Fin r → QQ := fun l => if l = i then 1 else af l with hadef
  have hai : a i = 1 := by rw [hadef]; exact if_pos rfl
  have ha_of_ne : ∀ l, l ≠ i → a l = af l := fun l hl => by rw [hadef]; exact if_neg hl
  have ha_cand : a ∈ cand i := by
    rw [hcanddef]
    refine Fintype.mem_piFinset.mpr fun l => ?_
    beta_reduce
    by_cases hl : l = i
    · rw [if_pos hl, Finset.mem_singleton, hl, hai]
    · rw [if_neg hl, Multiset.mem_toFinset, ha_of_ne l hl]
      exact haf_mem l hl
  have ha_le : ∀ l, μ (a l) ≤ 1 := by
    intro l
    by_cases hl : l = i
    · rw [hl, hai, map_one]
    · rw [ha_of_ne l hl]; exact haf_le l hl
  have hia : (⟨i, a⟩ : Σ _ : Fin r, Fin r → QQ) ∈ Finset.univ.sigma cand :=
    Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ha_cand⟩

  set D := ⨆ l, μ (xh l - a l) with hDdef
  have hDbound : 0 < D → Real.log η + 2 * (c * T) < 0 →
      (d : ℝ) * Real.log D ≤ Real.log η + 2 * (c * T) := by
    intro hD hX
    obtain ⟨l₀, hl₀⟩ := exists_eq_ciSup_of_finite (f := fun l => μ (xh l - a l))
    have hl₀i : l₀ ≠ i := by
      intro heq
      rw [heq, hxhi, hai, sub_self, map_zero] at hl₀
      have hD0 : D = 0 := by rw [hDdef]; exact hl₀.symm
      rw [hD0] at hD
      exact lt_irrefl _ hD
    have hbd := haf_bd l₀ hl₀i
    rw [← ha_of_ne l₀ hl₀i] at hbd
    have hl₀' : μ (xh l₀ - a l₀) = D := hl₀
    rw [hl₀'] at hbd
    have hgP : Real.exp (-(c * T)) ≤ ((Hf i l₀).eval 0).gaussNorm μ 1 := hPlow i l₀
    have hgPpos : 0 < ((Hf i l₀).eval 0).gaussNorm μ 1 := lt_of_lt_of_le (Real.exp_pos _) hgP
    have hDd : 0 < D ^ ((Hf i l₀).eval 0).natDegree := pow_pos hD _
    have h1 := Real.log_le_log (mul_pos hgPpos hDd) hbd
    rw [Real.log_mul hgPpos.ne' hDd.ne', Real.log_pow, Real.log_mul hBpos.ne' hη0.ne',
      Real.log_exp] at h1
    have h2 : -(c * T) ≤ Real.log (((Hf i l₀).eval 0).gaussNorm μ 1) := by
      have := Real.log_le_log (Real.exp_pos _) hgP
      rwa [Real.log_exp] at this
    have h3 : (((Hf i l₀).eval 0).natDegree : ℝ) * Real.log D ≤ Real.log η + 2 * (c * T) := by
      linarith
    have hlogD : Real.log D ≤ 0 := by
      by_contra hge
      push Not at hge
      have : 0 ≤ (((Hf i l₀).eval 0).natDegree : ℝ) * Real.log D :=
        mul_nonneg (Nat.cast_nonneg _) hge.le
      linarith
    have hd₀d : (((Hf i l₀).eval 0).natDegree : ℝ) ≤ d := by exact_mod_cast hd i l₀
    calc (d : ℝ) * Real.log D ≤ (((Hf i l₀).eval 0).natDegree : ℝ) * Real.log D :=
          mul_le_mul_of_nonpos_right hd₀d hlogD
      _ ≤ _ := h3

  have hfinal : (0 < D ∧ -Real.log D ≤ L) ∨ (0 < D ∧ -(κ * T) ≤ Real.log D) ∨
      -(κ * T) ≤ Real.log η ∨ 1 ≤ η :=
    hκ ⟨i, a⟩ hia μ hμ hμp R L hord hzero hxi hmax ha_le
  rcases hfinal with ⟨hD, h1⟩ | ⟨hD, h2⟩ | h3 | h4
  ·
    by_cases hX : Real.log η + 2 * (c * T) < 0
    · have h5 := hDbound hD hX
      have h6 : (d : ℝ) * (-L) ≤ (d : ℝ) * Real.log D :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg d)
      linarith
    · linarith
  ·
    by_cases hX : Real.log η + 2 * (c * T) < 0
    · have h5 := hDbound hD hX
      have h6 : (d : ℝ) * (-(κ * T)) ≤ (d : ℝ) * Real.log D :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)
      linarith
    · linarith
  ·
    linarith
  ·
    exact absurd h4 (not_le.mpr hη1)

end Main

end P2MC27

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (h : modularFunctionFieldBar N) (hh : h ≠ 0) (p : ℕ) (hp : p.Prime) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 < M ∧ ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      μ (p : AlgebraicClosure ℚ) < 1 →
      ∀ (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (L : ℝ), 0 ≤ L →
        (∀ Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 < Q.ord h →
            prox μ (evalVec s R) (evalVec s Q) ≤ L) →
        -(C * (-Real.log (μ (p : AlgebraicClosure ℚ)))) - M * L ≤ min 0 (Real.log (μ (R.evalAt h))) :=
  P2MC27.C2_main s hs h hh p hp

end P2MPiece4

end S_ModularCurve_exists_log_absValue_evalAt_ge_of_forall_prox_le
end P2MW
export P2MW.S_ModularCurve_exists_log_absValue_evalAt_ge_of_forall_prox_le (solution)
