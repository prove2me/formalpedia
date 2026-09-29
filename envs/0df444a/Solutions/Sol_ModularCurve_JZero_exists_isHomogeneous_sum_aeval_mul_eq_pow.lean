-- Prove2me | solution 1 for ModularCurve.JZero.exists_isHomogeneous_sum_aeval_mul_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4afe4b13-8f94-5f65-97cd-ae5553ba885e

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_RiemannRochRows
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_hasCanonicalDivisor_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_functionFieldRiemannRoch_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_degree_canonicalDivisorOf_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_genus_eq_genusFF_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_lSpace_eq_bot_of_degree_neg
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank
import Theorems.Thm_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_isHomogeneous_sum_aeval_mul_eq_pow
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

namespace P2MCert

open AlgebraicCurve ModularCurve Submodule KaehlerDifferential

variable {N : ℕ} [NeZero N]

local notation "𝕂" => AlgebraicClosure ℚ

theorem mul_mem_rr {K F : Type*} [Field K] [Field F] [Algebra K F]
    {A B : Divisor K F} {f g : F} (hf : f ∈ riemannRochSpace A) (hg : g ∈ riemannRochSpace B) :
    f * g ∈ riemannRochSpace (A + B) := by
  rw [mem_riemannRochSpace_iff] at hf hg ⊢
  intro w
  rcases eq_or_ne f 0 with rfl | hf0
  · left; rw [zero_mul]
  rcases eq_or_ne g 0 with rfl | hg0
  · left; rw [mul_zero]
  right
  rw [Place.ord_mul _ hf0 hg0, Finsupp.add_apply, neg_add]
  exact add_le_add ((hf w).resolve_left hf0) ((hg w).resolve_left hg0)

theorem rr_mul_le {K F : Type*} [Field K] [Field F] [Algebra K F] (A B : Divisor K F) :
    riemannRochSpace A * riemannRochSpace B ≤ riemannRochSpace (A + B) := by
  rw [mul_le]; intro f hf g hg; exact mul_mem_rr hf hg

theorem mem_span_pair_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {p₁ p₂ f : F} {W : Submodule K F}
    (hf : f ∈ span K {p₁, p₂} * W) : ∃ w₁ ∈ W, ∃ w₂ ∈ W, f = p₁ * w₁ + p₂ * w₂ := by
  rw [span_insert, Submodule.sup_mul, mem_sup] at hf
  obtain ⟨y, hy, z, hz, rfl⟩ := hf
  obtain ⟨w₁, hw₁, rfl⟩ := mem_span_singleton_mul.mp hy
  obtain ⟨w₂, hw₂, rfl⟩ := mem_span_singleton_mul.mp hz
  exact ⟨w₁, hw₁, w₂, hw₂, rfl⟩

theorem ell_eq_bar (N : ℕ) [NeZero N] (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hD : 2 * (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) - 1 ≤ Divisor.degree D) :
    (ell D : ℤ) = Divisor.degree D + 1 - (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by
  classical
  haveI hCO : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := isCurveOver_modularFunctionFieldBar N
  haveI hCD : HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N) :=
    hasCanonicalDivisor_modularFunctionFieldBar N
  haveI : Algebra.EssFiniteType (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := essFiniteType_modularFunctionFieldBar N
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  haveI hDCG : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    functionFieldRiemannRoch_modularFunctionFieldBar N
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[(modularFunctionFieldBar N)⁄(AlgebraicClosure ℚ)])
  have hdegK := degree_canonicalDivisorOf_modularFunctionFieldBar N hω
  have hgen := genus_eq_genusFF_modularFunctionFieldBar N
  have h1 := hRR hω D
  have hneg : Divisor.degree (canonicalDivisorOf hω - D) < 0 := by
    rw [map_sub, hdegK, hgen]; linarith
  have hell : ell (canonicalDivisorOf hω - D) = 0 := by
    show Module.finrank _ (LSpace _) = 0
    rw [AlgebraicCurve.lSpace_eq_bot_of_degree_neg hneg, finrank_bot]
  rw [hell, hgen] at h1
  push_cast at h1
  linarith

section Main

variable (N)
variable {a b : ℕ} (s : Fin a → ↥(modularFunctionFieldBar N)) (u : Fin b → ↥(modularFunctionFieldBar N))
  (hu : ∀ j, u j ≠ 0)
  (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
  (hd : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
  (hsD : span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
  (huD : ∀ j, u j ∈ riemannRochSpace D)
  (hbpf : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), ∃ j, w.ord (u j) + D w = 0)

include hd in

theorem finrank_rr_smul (m : ℤ) (hm : 1 ≤ m) :
    (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (m • D)) : ℤ)
      = m * D.degree + 1 - (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) := by
  have hg0 : (0 : ℤ) ≤ (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) := by exact_mod_cast Nat.zero_le _
  have := ell_eq_bar N (m • D) (by rw [map_zsmul, smul_eq_mul]; nlinarith)
  rw [map_zsmul, smul_eq_mul] at this
  exact this

include hd in
theorem finite_rr_smul (m : ℤ) (hm : 1 ≤ m) : FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace (m • D)) := by
  apply Module.finite_of_finrank_pos
  have hg0 : (0 : ℤ) ≤ (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) := by exact_mod_cast Nat.zero_le _
  have h := finrank_rr_smul N D hd m hm
  have : (0 : ℤ) < Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (m • D)) := by rw [h]; nlinarith
  exact_mod_cast this

include hu huD hbpf in

theorem exists_pencil : ∃ p : Fin 2 → ↥(modularFunctionFieldBar N),
    (∀ l, p l ∈ span (AlgebraicClosure ℚ) (Set.range u)) ∧ (∀ l, p l ≠ 0) ∧
    ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.ord (p 0) + D w = 0 ∨ w.ord (p 1) + D w = 0 := by
  classical
  haveI := hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  set V : Submodule (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) := span (AlgebraicClosure ℚ) (Set.range u) with hV
  haveI : FiniteDimensional (AlgebraicClosure ℚ) ↥V := FiniteDimensional.span_of_finite _ (Set.finite_range u)
  have hVD : V ≤ riemannRochSpace D := by rw [hV, span_le]; rintro _ ⟨j, rfl⟩; exact huD j
  have hbpfV : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), ∃ f ∈ V, f ≠ 0 ∧ w.ord f + D w = 0 :=
    fun w => by obtain ⟨j, hj⟩ := hbpf w; exact ⟨u j, subset_span ⟨j, rfl⟩, hu j, hj⟩
  obtain ⟨f₁, hf₁, f₂, hf₂, hpair⟩ :=
    AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace D V hVD hbpfV
  by_cases h10 : f₁ = 0
  · have key : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), f₂ ≠ 0 ∧ w.ord f₂ + D w = 0 :=
      fun w => (hpair w).resolve_left (fun h => h.1 h10)
    exact ⟨![f₂, f₂], fun l => by fin_cases l <;> exact hf₂, fun l => by fin_cases l <;> exact (key (cuspInftyBar N)).1,
      fun w => Or.inl (key w).2⟩
  · by_cases h20 : f₂ = 0
    · have key : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), f₁ ≠ 0 ∧ w.ord f₁ + D w = 0 :=
        fun w => (hpair w).resolve_right (fun h => h.1 h20)
      exact ⟨![f₁, f₁], fun l => by fin_cases l <;> exact hf₁, fun l => by fin_cases l <;> exact h10,
        fun w => Or.inl (key w).2⟩
    · exact ⟨![f₁, f₂], fun l => by fin_cases l <;> assumption, fun l => by fin_cases l <;> assumption,
        fun w => (hpair w).imp (fun h => h.2) (fun h => h.2)⟩

include hd in

theorem pencil_step (p : Fin 2 → ↥(modularFunctionFieldBar N)) (hp0 : ∀ l, p l ≠ 0)
    (hpD : ∀ l, p l ∈ riemannRochSpace D)
    (hpbpf : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), w.ord (p 0) + D w = 0 ∨ w.ord (p 1) + D w = 0)
    (m : ℤ) (hm : 2 ≤ m) :
    span (AlgebraicClosure ℚ) {p 0, p 1} * riemannRochSpace (m • D) = riemannRochSpace ((m + 1) • D) := by
  classical
  haveI := finite_rr_smul N D hd m (by omega)
  haveI := finite_rr_smul N D hd (m + 1) (by omega)
  have hp' : ∀ l, ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), 0 ≤ w.ord (p l) + D w :=
    fun l w => by have := (mem_riemannRochSpace_iff.mp (hpD l) w).resolve_left (hp0 l); linarith
  obtain ⟨hdim, hle⟩ := AlgebraicCurve.finrank_span_pair_mul_riemannRochSpace_add_finrank D (m • D)
    (hp0 0) (hp0 1) (hp' 0) (hp' 1) hpbpf
  rw [show m • D - D = (m - 1) • D by rw [sub_smul, one_smul]] at hdim
  rw [show m • D + D = (m + 1) • D by rw [add_smul, one_smul]] at hle
  apply Submodule.eq_of_le_of_finrank_le hle
  have h1 := finrank_rr_smul N D hd (m - 1) (by omega)
  have h2 := finrank_rr_smul N D hd m (by omega)
  have h3 := finrank_rr_smul N D hd (m + 1) (by omega)
  have hZ := congrArg (fun n : ℕ => (n : ℤ)) hdim
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hZ
  have : (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace ((m + 1) • D)) : ℤ)
      ≤ Module.finrank (AlgebraicClosure ℚ) ↥(span (AlgebraicClosure ℚ) {p 0, p 1} * riemannRochSpace (m • D)) := by
    rw [h1, h2] at hZ; rw [h3]; nlinarith
  exact_mod_cast this

end Main

end P2MCert

namespace P2MCert

open AlgebraicCurve ModularCurve Submodule MvPolynomial

section Homog

variable {R : Type*} [CommRing R] {σ : Type*}

theorem homogeneousComponent_of_isHomogeneous {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    homogeneousComponent n p = p := by
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule n p).mpr hp), if_pos rfl]

theorem homogeneousComponent_mul_deg_one (G P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) (m : ℕ) :
    homogeneousComponent (m + 1) (G * P) = homogeneousComponent m G * P := by
  classical
  ext d
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases hd : Finsupp.degree d = m + 1
  · rw [if_pos hd]
    apply Finset.sum_congr rfl
    intro x hx
    rw [coeff_homogeneousComponent]
    by_cases hP0 : coeff x.2 P = 0
    · rw [hP0, mul_zero, mul_zero]
    · have h2 : Finsupp.degree x.2 = 1 := by
        by_contra hne; exact hP0 (hP.coeff_eq_zero hne)
      have h12 : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
      have h1 : Finsupp.degree x.1 = m := by
        have := congrArg Finsupp.degree h12
        rw [map_add, h2, hd] at this
        omega
      rw [if_pos h1]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    rw [coeff_homogeneousComponent]
    split_ifs with h1
    · by_cases hP0 : coeff x.2 P = 0
      · rw [hP0, mul_zero]
      · exfalso
        have h2 : Finsupp.degree x.2 = 1 := by
          by_contra hne; exact hP0 (hP.coeff_eq_zero hne)
        have h12 : x.1 + x.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
        apply hd
        have := congrArg Finsupp.degree h12
        rw [map_add, h2, h1] at this
        exact this.symm
    · rw [zero_mul]

theorem isHomogeneous_det_of_forall {t : ℕ} (A : Matrix (Fin t) (Fin t) (MvPolynomial σ R))
    (hA : ∀ i j, (A i j).IsHomogeneous 3) : (A.det).IsHomogeneous (3 * t) := by
  classical
  rw [Matrix.det_apply']
  apply IsHomogeneous.sum
  intro τ _
  have hprod : (∏ i, A (τ i) i).IsHomogeneous (3 * t) := by
    have := IsHomogeneous.prod Finset.univ (fun i => A (τ i) i) (fun _ => 3) (fun i _ => hA _ _)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm] using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h
  · rw [h]; simpa using hprod
  · rw [h]; simpa using hprod.neg

end Homog

section Cert

local notation "𝕂" => AlgebraicClosure ℚ

set_option maxHeartbeats 12800000 in
theorem cert (N : ℕ) [NeZero N]
    {a b : ℕ} (s : Fin a → ↥(modularFunctionFieldBar N)) (u : Fin b → ↥(modularFunctionFieldBar N))
    (hu : ∀ j, u j ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hd : 2 * (genusFF (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : span (AlgebraicClosure ℚ) (Set.range s) = riemannRochSpace D)
    (huD : ∀ j, u j ∈ riemannRochSpace D)
    (hbpf : ∀ w : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N), ∃ j, w.ord (u j) + D w = 0) :
    ∃ M : ℕ, ∀ k : Fin a, ∃ q : Fin b → MvPolynomial (Fin a) (AlgebraicClosure ℚ),
      (∀ j, (q j).IsHomogeneous M) ∧
      ∑ j, MvPolynomial.aeval s (q j) * u j = s k ^ (M + 1) := by
  classical

  obtain ⟨p, hpV, hp0, hpbpf⟩ := exists_pencil N u hu D huD hbpf
  have hle_uD : span 𝕂 (Set.range u) ≤ riemannRochSpace D := by
    rw [span_le]; rintro _ ⟨j, rfl⟩; exact huD j
  have hpD : ∀ l, p l ∈ riemannRochSpace D := fun l => hle_uD (hpV l)
  have hlam' : ∀ l, ∃ c : Fin b → 𝕂, ∑ j, c j • u j = p l := fun l => (mem_span_range_iff_exists_fun 𝕂).mp (hpV l)
  choose lam hlam using hlam'
  have hcu' : ∀ j, ∃ c : Fin a → 𝕂, ∑ i, c i • s i = u j := fun j =>
    (mem_span_range_iff_exists_fun 𝕂).mp (by rw [hsD]; exact huD j)
  choose cu hcu using hcu'

  let Pl : Fin 2 → MvPolynomial (Fin a) 𝕂 := fun l => ∑ j, lam l j • ∑ i, cu j i • X i
  have hPl_hom : ∀ l, (Pl l).IsHomogeneous 1 := by
    intro l
    apply IsHomogeneous.sum; intro j _
    rw [smul_eq_C_mul]; apply IsHomogeneous.C_mul
    apply IsHomogeneous.sum; intro i _
    rw [smul_eq_C_mul]; exact (isHomogeneous_X 𝕂 i).C_mul _
  have hPl_eval : ∀ l, aeval s (Pl l) = p l := by
    intro l
    simp only [Pl, map_sum, map_smul, aeval_X]
    rw [← hlam l]
    exact Finset.sum_congr rfl fun j _ => by rw [hcu j]
  let I : Ideal (MvPolynomial (Fin a) 𝕂) := Ideal.span {Pl 0, Pl 1}
  have hPlI : ∀ l, Pl l ∈ I := by
    intro l; apply Ideal.subset_span
    fin_cases l
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)

  have hW : ∀ m : ℤ, 2 ≤ m → span 𝕂 {p 0, p 1} * riemannRochSpace (m • D) = riemannRochSpace ((m + 1) • D) :=
    fun m hm => pencil_step N D hd p hp0 hpD hpbpf m hm
  have step : ∀ (m : ℤ), 2 ≤ m → ∀ f ∈ riemannRochSpace ((m + 1) • D),
      ∃ w : Fin 2 → ↥(modularFunctionFieldBar N), (∀ l, w l ∈ riemannRochSpace (m • D)) ∧ f = ∑ l, p l * w l := by
    intro m hm f hf
    rw [← hW m hm] at hf
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := mem_span_pair_mul hf
    exact ⟨![w₁, w₂], fun l => by fin_cases l <;> assumption, by simp [Fin.sum_univ_two]⟩

  haveI hfin2 : FiniteDimensional 𝕂 ↥(riemannRochSpace ((2 : ℤ) • D)) := finite_rr_smul N D hd 2 (by norm_num)
  set t : ℕ := Module.finrank 𝕂 ↥(riemannRochSpace ((2 : ℤ) • D)) with ht
  let B := Module.finBasis 𝕂 ↥(riemannRochSpace ((2 : ℤ) • D))
  let n : Fin t → ↥(modularFunctionFieldBar N) := fun β => (B β : ↥(modularFunctionFieldBar N))
  have ht1 : 1 ≤ t := by
    have h := finrank_rr_smul N D hd 2 (by norm_num)
    have hg0 : (0 : ℤ) ≤ (genusFF 𝕂 ↥(modularFunctionFieldBar N) : ℤ) := by exact_mod_cast Nat.zero_le _
    have : (1 : ℤ) ≤ Module.finrank 𝕂 ↥(riemannRochSpace ((2 : ℤ) • D)) := by rw [h]; nlinarith
    rw [ht]; exact_mod_cast this
  have hn0 : n ≠ 0 := by
    intro h
    have := congrFun h ⟨0, ht1⟩
    exact B.ne_zero ⟨0, ht1⟩ (Subtype.ext this)

  have hsD1 : ∀ i, s i ∈ riemannRochSpace D := by
    intro i; rw [← hsD]; exact subset_span ⟨i, rfl⟩
  refine ⟨3 * t - 1, fun k => ?_⟩

  have hmem5 : ∀ β, s k ^ 3 * n β ∈ riemannRochSpace (((4 : ℤ) + 1) • D) := by
    intro β
    have h3 : s k ^ 3 ∈ riemannRochSpace (D + D + D) := by
      rw [pow_succ, pow_two]; exact mul_mem_rr (mul_mem_rr (hsD1 k) (hsD1 k)) (hsD1 k)
    have := mul_mem_rr h3 (B β).2
    have hdiv : D + D + D + (2 : ℤ) • D = ((4 : ℤ) + 1) • D := by module
    rw [hdiv] at this
    exact this
  have hdec : ∀ β, ∃ g : Fin 2 → Fin 2 → Fin 2 → ↥(modularFunctionFieldBar N),
      (∀ l₀ l₁ l₂, g l₀ l₁ l₂ ∈ riemannRochSpace ((2 : ℤ) • D)) ∧
      s k ^ 3 * n β = ∑ l₀, ∑ l₁, ∑ l₂, p l₀ * (p l₁ * (p l₂ * g l₀ l₁ l₂)) := by
    intro β
    obtain ⟨w, hw, hweq⟩ := step 4 (by norm_num) _ (hmem5 β)
    have hw' : ∀ l, ∃ w' : Fin 2 → ↥(modularFunctionFieldBar N),
        (∀ l', w' l' ∈ riemannRochSpace ((3 : ℤ) • D)) ∧ w l = ∑ l', p l' * w' l' :=
      fun l => step 3 (by norm_num) (w l) (by have := hw l; norm_num at this ⊢; exact this)
    choose w2 hw2 hw2eq using hw'
    have hw'' : ∀ l l', ∃ w' : Fin 2 → ↥(modularFunctionFieldBar N),
        (∀ l'', w' l'' ∈ riemannRochSpace ((2 : ℤ) • D)) ∧ w2 l l' = ∑ l'', p l'' * w' l'' :=
      fun l l' => step 2 le_rfl (w2 l l') (by have := hw2 l l'; norm_num at this ⊢; exact this)
    choose w3 hw3 hw3eq using hw''
    refine ⟨w3, hw3, ?_⟩
    rw [hweq]
    simp only [hw2eq, hw3eq, Finset.mul_sum]
  choose g hg hgeq using hdec

  let μ : Fin t → Fin 2 → Fin 2 → Fin 2 → Fin t → 𝕂 := fun β l₀ l₁ l₂ γ => B.repr ⟨g β l₀ l₁ l₂, hg β l₀ l₁ l₂⟩ γ
  have hgμ : ∀ β l₀ l₁ l₂, g β l₀ l₁ l₂ = ∑ γ, μ β l₀ l₁ l₂ γ • n γ := by
    intro β l₀ l₁ l₂
    have h1 : ((⟨g β l₀ l₁ l₂, hg β l₀ l₁ l₂⟩ : ↥(riemannRochSpace ((2 : ℤ) • D))) : ↥(modularFunctionFieldBar N))
        = ∑ γ, μ β l₀ l₁ l₂ γ • n γ := by
      conv_lhs => rw [← B.sum_repr ⟨g β l₀ l₁ l₂, hg β l₀ l₁ l₂⟩]
      rw [Submodule.coe_sum]
      rfl
    exact h1

  let Cm : Matrix (Fin t) (Fin t) (MvPolynomial (Fin a) 𝕂) :=
    fun β γ => ∑ l₀, ∑ l₁, ∑ l₂, μ β l₀ l₁ l₂ γ • (Pl l₀ * (Pl l₁ * Pl l₂))
  have hCm_hom : ∀ β γ, (Cm β γ).IsHomogeneous 3 := by
    intro β γ
    apply IsHomogeneous.sum; intro l₀ _; apply IsHomogeneous.sum; intro l₁ _; apply IsHomogeneous.sum; intro l₂ _
    rw [smul_eq_C_mul]
    exact ((hPl_hom l₀).mul ((hPl_hom l₁).mul (hPl_hom l₂))).C_mul _
  have hCm_I : ∀ β γ, Cm β γ ∈ I := by
    intro β γ
    refine Ideal.sum_mem _ fun l₀ _ => Ideal.sum_mem _ fun l₁ _ => Ideal.sum_mem _ fun l₂ _ => ?_
    rw [smul_eq_C_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hPlI l₀))
  have hCm_eval : ∀ β γ, aeval s (Cm β γ) = ∑ l₀, ∑ l₁, ∑ l₂, μ β l₀ l₁ l₂ γ • (p l₀ * (p l₁ * p l₂)) := by
    intro β γ
    simp only [Cm, map_sum, map_smul, map_mul, hPl_eval]

  have hrel : ∀ β, s k ^ 3 * n β = ∑ γ, aeval s (Cm β γ) * n γ := by
    intro β
    rw [hgeq β]
    simp only [hgμ, hCm_eval, Finset.mul_sum, Finset.sum_mul, Algebra.smul_def]

    conv_rhs => rw [Finset.sum_comm]
    conv_rhs => enter [2, l₀]; rw [Finset.sum_comm]
    conv_rhs => enter [2, l₀, 2, l₁]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l₀ _ => Finset.sum_congr rfl fun l₁ _ =>
      Finset.sum_congr rfl fun l₂ _ => Finset.sum_congr rfl fun γ _ => ?_
    ring

  let ev3 : Polynomial (MvPolynomial (Fin a) 𝕂) →+* MvPolynomial (Fin a) 𝕂 := Polynomial.evalRingHom (X k ^ 3)
  let A : Matrix (Fin t) (Fin t) (MvPolynomial (Fin a) 𝕂) := ev3.mapMatrix (Matrix.charmatrix Cm)
  have hA : ∀ β γ, A β γ = (if β = γ then X k ^ 3 else 0) - Cm β γ := by
    intro β γ
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply, map_sub, Matrix.diagonal_apply]
    congr 1
    · split_ifs <;> simp [ev3]
    · simp [ev3]
  have hA_hom : ∀ β γ, (A β γ).IsHomogeneous 3 := by
    intro β γ
    rw [hA]
    refine IsHomogeneous.sub ?_ (hCm_hom β γ)
    split_ifs
    · exact isHomogeneous_X_pow k 3
    · exact isHomogeneous_zero _ _ _

  have hmulVec : Matrix.mulVec (A.map (aeval s)) n = 0 := by
    funext β
    show ∑ γ, (A.map (aeval s)) β γ * n γ = 0
    simp only [Matrix.map_apply, hA, map_sub]
    have : ∑ γ, (aeval s (if β = γ then (X k ^ 3 : MvPolynomial (Fin a) 𝕂) else 0) - aeval s (Cm β γ)) * n γ
        = s k ^ 3 * n β - ∑ γ, aeval s (Cm β γ) * n γ := by
      rw [Finset.sum_congr rfl fun γ _ => sub_mul _ _ (n γ), Finset.sum_sub_distrib]
      congr 1
      rw [Finset.sum_eq_single β]
      · simp [aeval_X]
      · intro γ _ hγ; rw [if_neg (Ne.symm hγ), map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ β) h
    rw [this, hrel β, sub_self]
  have hdetA : aeval s A.det = 0 := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨n, hn0, hmulVec⟩

  have hdet_eq : A.det = ev3 (Matrix.charpoly Cm) := by
    show (ev3.mapMatrix (Matrix.charmatrix Cm)).det = _
    rw [← RingHom.map_det]; rfl
  have hmonic := Matrix.charpoly_monic Cm
  have hdeg : (Matrix.charpoly Cm).natDegree = t := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  set h : MvPolynomial (Fin a) 𝕂 :=
    ∑ i ∈ Finset.range t, (Matrix.charpoly Cm).coeff i * (X k ^ 3) ^ i with hh
  have hdet_sum : A.det = X k ^ (3 * t) + h := by
    rw [hdet_eq, hmonic.as_sum, hdeg]
    simp only [ev3, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, hh]
    rw [← pow_mul, mul_comm 3 t, mul_comm t 3]
  have hhI : h ∈ I := by
    refine Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ ?_
    have hlt : i < t := Finset.mem_range.mp hi
    have := Matrix.coeff_charpoly_mem_ideal_pow (M := Cm) (I := I) hCm_I i
    rw [Fintype.card_fin] at this
    exact Ideal.pow_le_self (by omega) this
  have hdet_hom : A.det.IsHomogeneous (3 * t) := isHomogeneous_det_of_forall A hA_hom
  have hh_hom : h.IsHomogeneous (3 * t) := by
    have : h = A.det - X k ^ (3 * t) := by rw [hdet_sum]; ring
    rw [this]
    exact hdet_hom.sub (isHomogeneous_X_pow k (3 * t))

  obtain ⟨G₀, G₁, hG⟩ := Ideal.mem_span_pair.mp hhI
  let H : Fin 2 → MvPolynomial (Fin a) 𝕂 := fun l => homogeneousComponent (3 * t - 1) (![G₀, G₁] l)
  have hH_hom : ∀ l, (H l).IsHomogeneous (3 * t - 1) := fun l => homogeneousComponent_isHomogeneous _ _
  have h3t : 3 * t - 1 + 1 = 3 * t := by omega
  have hH : H 0 * Pl 0 + H 1 * Pl 1 = h := by
    have := congrArg (homogeneousComponent (3 * t)) hG
    rw [map_add, ← h3t, homogeneousComponent_mul_deg_one G₀ (Pl 0) (hPl_hom 0),
      homogeneousComponent_mul_deg_one G₁ (Pl 1) (hPl_hom 1), h3t,
      homogeneousComponent_of_isHomogeneous hh_hom] at this
    simpa [H] using this

  refine ⟨fun j => ∑ l, C (-lam l j) * H l, fun j => ?_, ?_⟩
  · exact IsHomogeneous.sum _ _ _ fun l _ => (hH_hom l).C_mul _
  ·
    have hXk : aeval s (X k ^ (3 * t) : MvPolynomial (Fin a) 𝕂) = s k ^ (3 * t) := by rw [map_pow, aeval_X]
    have key : s k ^ (3 * t) = -(aeval s (H 0) * p 0 + aeval s (H 1) * p 1) := by
      have h1 : aeval s A.det = aeval s (X k ^ (3 * t) : MvPolynomial (Fin a) 𝕂) + aeval s h := by rw [hdet_sum, map_add]
      rw [hdetA, hXk] at h1
      have h2 : aeval s h = aeval s (H 0) * p 0 + aeval s (H 1) * p 1 := by
        rw [← hH, map_add, map_mul, map_mul, hPl_eval, hPl_eval]
      linear_combination -h1 - h2
    rw [h3t, key]
    have aux : ∀ j, aeval s (∑ l, C (-lam l j) * H l) * u j = ∑ l, -(lam l j • (aeval s (H l) * u j)) := by
      intro j
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, MvPolynomial.aeval_C, map_neg, Algebra.smul_def]; ring
    simp_rw [aux]
    rw [Finset.sum_comm, Fin.sum_univ_two]
    have aux2 : ∀ l, ∑ j, -(lam l j • (aeval s (H l) * u j)) = -(aeval s (H l) * p l) := by
      intro l
      rw [Finset.sum_neg_distrib, ← hlam l, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm]
    rw [aux2 0, aux2 1, neg_add]

end Cert

end P2MCert

open AlgebraicCurve ModularCurve in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N]
    {a b : ℕ} (s : Fin a → ↥(ModularCurve.modularFunctionFieldBar N)) (u : Fin b → ↥(ModularCurve.modularFunctionFieldBar N))
    (hu : ∀ j, u j ≠ 0)
    (D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hd : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ D.degree)
    (hsD : Submodule.span (AlgebraicClosure ℚ) (Set.range s) = AlgebraicCurve.riemannRochSpace D)
    (huD : ∀ j, u j ∈ AlgebraicCurve.riemannRochSpace D)
    (hbpf : ∀ w : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      ∃ j, w.ord (u j) + D w = 0) :
    ∃ M : ℕ, ∀ k : Fin a, ∃ q : Fin b → MvPolynomial (Fin a) (AlgebraicClosure ℚ),
      (∀ j, (q j).IsHomogeneous M) ∧
      ∑ j, MvPolynomial.aeval s (q j) * u j = s k ^ (M + 1) :=
  P2MCert.cert N s u hu D hd hsD huD hbpf

end S_ModularCurve_JZero_exists_isHomogeneous_sum_aeval_mul_eq_pow
end P2MW
export P2MW.S_ModularCurve_JZero_exists_isHomogeneous_sum_aeval_mul_eq_pow (solution)
