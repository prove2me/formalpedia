-- Prove2me | solution 1 for ModularCurve.JZero.riemannRochSpace_embDivisor_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/a8fcb02c-932f-52ce-ba17-fbb5eb77605c

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
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import Theorems.Thm_AlgebraicCurve_finrank_span_pair_mul_riemannRochSpace_add_finrank
import Theorems.Thm_AlgebraicCurve_exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_eq
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace P2MBrickPN

open AlgebraicCurve ModularCurve Submodule KaehlerDifferential

theorem riemannRochSpace_mono {K F : Type*} [Field K] [Field F] [Algebra K F] {D D' : Divisor K F} (h : D ≤ D') :
    riemannRochSpace D ≤ riemannRochSpace D' := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro v
  rcases hf v with h0 | h1
  · exact Or.inl h0
  · exact Or.inr ((neg_le_neg (h v)).trans h1)

theorem mul_mem_riemannRochSpace_add' {K F : Type*} [Field K] [Field F] [Algebra K F]
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

theorem riemannRochSpace_mul_le {K F : Type*} [Field K] [Field F] [Algebra K F] (A B : Divisor K F) :
    riemannRochSpace A * riemannRochSpace B ≤ riemannRochSpace (A + B) := by
  rw [mul_le]
  intro f hf g hg
  exact mul_mem_riemannRochSpace_add' hf hg

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

set_option maxHeartbeats 3200000 in

theorem main (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k) :
    riemannRochSpace (embDivisor N) * riemannRochSpace ((k : ℤ) • embDivisor N)
      = riemannRochSpace ((k + 1 : ℤ) • embDivisor N) := by
  classical
  set E := embDivisor N with hEdef
  set g : ℤ := (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) with hgdef
  have hg0 : 0 ≤ g := by rw [hgdef]; exact_mod_cast Nat.zero_le _
  haveI hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    hasPrincipalDivisors_modularFunctionFieldBar_unconditional N

  have hdegE : Divisor.degree E = 2 * g + 1 := by
    rw [hEdef, embDivisor, map_zsmul, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]
    simp [embDegree, hgdef]
  have hdeg : ∀ m : ℤ, Divisor.degree (m • E) = m * (2 * g + 1) := fun m => by
    rw [map_zsmul, hdegE, smul_eq_mul]

  have hellm : ∀ m : ℤ, 1 ≤ m →
      (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (m • E)) : ℤ) = m * (2 * g + 1) + 1 - g := by
    intro m hm
    have := ell_eq_bar N (m • E) (by rw [hdeg]; nlinarith)
    rw [hdeg] at this
    exact this

  have hfin : ∀ m : ℤ, 1 ≤ m → FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace (m • E)) := by
    intro m hm
    apply Module.finite_of_finrank_pos
    have := hellm m hm
    have : (0 : ℤ) < Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (m • E)) := by rw [this]; nlinarith
    exact_mod_cast this
  have hE1 : (1 : ℤ) • E = E := one_smul _ _
  haveI hfinE : FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by
    have := hfin 1 le_rfl
    rwa [hE1] at this
  haveI := hfin (k : ℤ) (by exact_mod_cast (by omega : 1 ≤ k))
  haveI := hfin ((k : ℤ) + 1) (by omega)

  have hbpf : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      ∃ f ∈ riemannRochSpace E, f ≠ 0 ∧ w.ord f + E w = 0 := by
    intro w
    have hsub : riemannRochSpace (E - Finsupp.single w 1) ≤ riemannRochSpace E :=
      riemannRochSpace_mono (by
        intro v; simp only [Finsupp.sub_apply, Finsupp.single_apply]; split_ifs <;> omega)
    have hlt : Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (E - Finsupp.single w 1))
        < Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by
      have h1 : (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (E - Finsupp.single w 1)) : ℤ)
          = 2 * g - g + 1 := by
        have := ell_eq_bar N (E - Finsupp.single w 1)
          (by rw [map_sub, hdegE, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar]; push_cast; linarith)
        rw [map_sub, hdegE, Divisor.degree_single, deg_eq_one_modularFunctionFieldBar] at this
        push_cast at this
        show (ell (E - Finsupp.single w 1) : ℤ) = _
        linarith
      have h2 : (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) : ℤ) = 2 * g + 1 + 1 - g := by
        have := hellm 1 le_rfl
        rwa [hE1, one_mul] at this
      have : (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (E - Finsupp.single w 1)) : ℤ)
          < Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by rw [h1, h2]; linarith
      exact_mod_cast this
    obtain ⟨u, huE, hunot⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hsub fun heq => by rw [heq] at hlt; exact lt_irrefl _ hlt)
    have hu0 : u ≠ 0 := fun h0 => hunot (h0 ▸ Submodule.zero_mem _)
    refine ⟨u, huE, hu0, ?_⟩
    have hge := (mem_riemannRochSpace_iff.mp huE w).resolve_left hu0
    by_contra hne
    apply hunot
    rw [mem_riemannRochSpace_iff]
    intro v
    right
    rw [Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs with hvw
    · subst hvw; omega
    · rw [sub_zero]; exact (mem_riemannRochSpace_iff.mp huE v).resolve_left hu0

  obtain ⟨f₁, hf₁E, f₂, hf₂E, hpair⟩ :=
    AlgebraicCurve.exists_pair_forall_ord_add_eq_zero_of_subset_riemannRochSpace E (riemannRochSpace E) le_rfl hbpf

  have hsel : ∃ p₁ p₂ : modularFunctionFieldBar N,
      p₁ ∈ riemannRochSpace E ∧ p₂ ∈ riemannRochSpace E ∧ p₁ ≠ 0 ∧ p₂ ≠ 0 ∧
      ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), w.ord p₁ + E w = 0 ∨ w.ord p₂ + E w = 0 := by
    by_cases h10 : f₁ = 0
    · have key : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), f₂ ≠ 0 ∧ w.ord f₂ + E w = 0 :=
        fun w => (hpair w).resolve_left (fun h => h.1 h10)
      exact ⟨f₂, f₂, hf₂E, hf₂E, (key (cuspInftyBar N)).1, (key (cuspInftyBar N)).1, fun w => Or.inl (key w).2⟩
    · by_cases h20 : f₂ = 0
      · have key : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), f₁ ≠ 0 ∧ w.ord f₁ + E w = 0 :=
          fun w => (hpair w).resolve_right (fun h => h.1 h20)
        exact ⟨f₁, f₁, hf₁E, hf₁E, h10, h10, fun w => Or.inl (key w).2⟩
      · exact ⟨f₁, f₂, hf₁E, hf₂E, h10, h20, fun w => (hpair w).imp (fun h => h.2) (fun h => h.2)⟩
  obtain ⟨p₁, p₂, hp₁E, hp₂E, hp₁0, hp₂0, hpbpf⟩ := hsel
  have hp₁' : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ w.ord p₁ + E w :=
    fun w => by have := (mem_riemannRochSpace_iff.mp hp₁E w).resolve_left hp₁0; linarith
  have hp₂' : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ w.ord p₂ + E w :=
    fun w => by have := (mem_riemannRochSpace_iff.mp hp₂E w).resolve_left hp₂0; linarith

  obtain ⟨hdim, -⟩ := AlgebraicCurve.finrank_span_pair_mul_riemannRochSpace_add_finrank E ((k : ℤ) • E)
    hp₁0 hp₂0 hp₁' hp₂' hpbpf
  have hsubE : (k : ℤ) • E - E = ((k : ℤ) - 1) • E := by rw [sub_smul, one_smul]
  rw [hsubE] at hdim

  have hk1 : (1 : ℤ) ≤ (k : ℤ) - 1 := by omega
  have hdimZ : (Module.finrank (AlgebraicClosure ℚ) ↥(span (AlgebraicClosure ℚ) {p₁, p₂} * riemannRochSpace ((k : ℤ) • E)) : ℤ)
      = ((k : ℤ) + 1) * (2 * g + 1) + 1 - g := by
    have h := congrArg (fun n : ℕ => (n : ℤ)) hdim
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
    rw [hellm _ hk1, hellm _ (by exact_mod_cast (by omega : 1 ≤ k))] at h
    linarith
  have htarget := hellm ((k : ℤ) + 1) (by omega)

  have hspan_le : span (AlgebraicClosure ℚ) {p₁, p₂} ≤ riemannRochSpace E := by
    rw [span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hp₁E
    · exact hp₂E
  have hprod_le : riemannRochSpace E * riemannRochSpace ((k : ℤ) • E) ≤ riemannRochSpace (((k : ℤ) + 1) • E) := by
    have := riemannRochSpace_mul_le E ((k : ℤ) • E)
    rwa [show E + (k : ℤ) • E = ((k : ℤ) + 1) • E by rw [add_smul, one_smul, add_comm]] at this
  have hchain : span (AlgebraicClosure ℚ) {p₁, p₂} * riemannRochSpace ((k : ℤ) • E)
      ≤ riemannRochSpace E * riemannRochSpace ((k : ℤ) • E) := mul_le_mul_left hspan_le _
  apply le_antisymm hprod_le

  have heq : span (AlgebraicClosure ℚ) {p₁, p₂} * riemannRochSpace ((k : ℤ) • E)
      = riemannRochSpace (((k : ℤ) + 1) • E) := by
    apply Submodule.eq_of_le_of_finrank_le (hchain.trans hprod_le)
    have : (Module.finrank (AlgebraicClosure ℚ) ↥(riemannRochSpace (((k : ℤ) + 1) • E)) : ℤ)
        ≤ Module.finrank (AlgebraicClosure ℚ) ↥(span (AlgebraicClosure ℚ) {p₁, p₂} * riemannRochSpace ((k : ℤ) • E)) := by
      rw [hdimZ, htarget]
    exact_mod_cast this
  rw [← heq]
  exact hchain

end P2MBrickPN

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (N : ℕ) [NeZero N] (k : ℕ) (hk : 2 ≤ k) :
    AlgebraicCurve.riemannRochSpace (ModularCurve.embDivisor N)
        * AlgebraicCurve.riemannRochSpace ((k : ℤ) • ModularCurve.embDivisor N)
      = AlgebraicCurve.riemannRochSpace ((k + 1 : ℤ) • ModularCurve.embDivisor N) :=
  P2MBrickPN.main N k hk

end S_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_eq
end P2MW
export P2MW.S_ModularCurve_JZero_riemannRochSpace_embDivisor_mul_eq (solution)
