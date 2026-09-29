-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3db382d2-f7ce-5bed-b489-6c97ad345f1e

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_measurable_bounded_compactArch_integral_pos_on_thirdRow_window
import Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay
import Theorems.Thm_LanglandsTunnell_CubicInduction_measurable_gauge3
import Theorems.Thm_LanglandsTunnell_CubicInduction_ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_isSlabDomain
import Theorems.Thm_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Theorems.Thm_LanglandsTunnell_CubicInduction_norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth
import Theorems.Thm_LanglandsTunnell_CubicInduction_mem_cuspFunctions_of_isCuspidalAlong_of_archDeriv_growth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one"
p2m_attr_erase "simp" "AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory NumberField.StandardAddChar
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous u)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) u)
    (hsm : ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, u (g * localToAdelic3 v k) = u g)
    (hsa : WhittakerBlock.IsArchSmooth3 u)
    (hKf : ∃ s : Finset (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ,
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k = 1) → archComponent3 (𝓞 ℚ) ℚ k ∈ orth3 →
        (fun g => u (g * k)) ∈ Submodule.span ℂ (s : Set (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)))
    (hcw : ∀ w : List (Fin 3 × Fin 3),
      Continuous (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w))
    (N : ℕ) (hgr : ∀ w : List (Fin 3 × Fin 3), ∃ C : ℝ, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      ‖List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) u w g‖ ≤ C * gauge3 ℚ g ^ N)
    (B : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hB : IsCompact B) (b₀ : ℝ) (hb₀ : 1 < b₀) :
    ∃ (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (φ₀ : ℝ), 0 < φ₀ ∧
      (∀ k ∈ B, ∀ a : Fin 3 → ℝ, (∀ i, 0 < a i) → b₀⁻¹ ≤ a 2 → a 2 ≤ b₀ →
        φ₀ ≤ ‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                      AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖) ∧
      ∃ C' : ℝ, ∀ σ : ℝ, σ ∈ Set.Ioc (1 : ℝ) 2 →
      (letI : MeasurableSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
        ∫⁻ k in B, (∫⁻ a in Set.pi Set.univ (fun _ : Fin 3 => Set.Ioi (0 : ℝ)),
            (‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
                  NumberField.StandardAddChar.psiQ u
                  (WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k)‖₊ : ℝ≥0∞) ^ 2 *
              (‖Φ fun j : Fin 3 => ((WhittakerBlock.archRealLift3 (fun i j => if i = j then a i else 0) * k :
                  AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) 2 j‖₊ : ℝ≥0∞) *
              ENNReal.ofReal (a 0 ^ (σ - 3) * a 1 ^ (σ - 1) * a 2 ^ (σ + 1)) ∂volume)
          ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) ≤
          ENNReal.ofReal (C' / (σ - 1))) := by
  classical

  obtain ⟨Φ₀, hΦ₀⟩ := SlabL2.exists_isSlabDomain 1 2 one_pos one_lt_two

  have hu : u ∈ cuspFunctions ω 1 2 Φ₀ :=
    mem_cuspFunctions_of_isCuspidalAlong_of_archDeriv_growth ω hω u hc haut hP21 hP12 S hK hsm hsa hcw N hgr hcen
      1 2 Φ₀ hΦ₀

  obtain ⟨cS, CS, hcS, hcover⟩ := exists_mul_eq_unipotent_mul_diagonal_mul_compact
  have hSfin := adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top cS CS hcS 1 2 one_pos one_lt_two

  have hdecay := norm_mul_gauge3_pow_le_of_siegel_of_isCuspidalAlong_of_archDeriv_growth u hc haut hP21 hP12 S hK hsm
    hsa hcw N hgr cS CS 1 2 hcS one_pos one_lt_two

  obtain ⟨C₁, hC₁, htorus⟩ := exists_lintegral_torus_whittaker3_sq_le_mul_lintegral_quotientMeasure B hB

  obtain ⟨Φ, M, R₀, Nf, φ₀, hR₀, hNf, hφ₀, hΦm, hΦM, hΦsupp, hΦfin, hΦwin⟩ :=
    exists_measurable_bounded_compactArch_integral_pos_on_thirdRow_window B hB b₀ hb₀

  have GAP2 : Measurable (gauge3 ℚ) := measurable_gauge3

  letI : MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) := AdelicEpstein.unitIdeleMeasurableSpace
  let du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) := Measure.dirac 1

  obtain ⟨c₂, hc₂, hc₂', hunfold⟩ :=
    exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure ω hω 1 2 Φ₀ hΦ₀ du

  obtain ⟨hdet1, hslab⟩ := ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
  have GAP5 : ∃ Sg : Set (AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ᵐ x ∂(SlabL2.slabMeasure 1 2), ∃ γ : GL (Fin 3) ℚ, globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Sg) ∧
      SlabL2.slabMeasure 1 2 Sg < ⊤ ∧
      (∀ K : ℕ, ∃ C : ℝ, ∀ g ∈ Sg, ‖u g‖ * gauge3 ℚ g ^ K ≤ C) := by
    refine ⟨{g : AdelicGL 3 (𝓞 ℚ) ℚ | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
          (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
          ∀ w : InfinitePlace ℚ,
            (∀ i j : Fin 3,
              (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
              (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
              ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ CS) ∧
            (∀ i j : Fin 3, i ≠ j →
              (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
            cS ≤ archRoot₁ ℚ w t ∧ cS ≤ archRoot₂ ℚ w t ∧
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1} ∩
        {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc 1 2}, ?_, ?_, ?_⟩
    · rw [SlabL2.slabMeasure_def]
      refine (ae_restrict_iff' (hslab 1 2)).2 (ae_of_all _ fun x hx => ?_)
      obtain ⟨γ, n, t, k, hγ, hn, ht', hk, harch⟩ := hcover x
      refine ⟨γ, ⟨n, t, k, hγ, hn, ht', hk, harch⟩, ?_⟩
      show NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ * x)) ∈ Set.Icc 1 2
      rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, hdet1, one_mul]
      exact hx
    · rw [SlabL2.slabMeasure_def]
      exact lt_of_le_of_lt (Measure.le_iff'.1 Measure.restrict_le_self _) hSfin
    · intro K
      obtain ⟨C', hC'⟩ := hdecay K
      refine ⟨C', fun g hg => ?_⟩
      obtain ⟨⟨n, t, k, rfl, hn, ht', hk, harch⟩, hgslab⟩ := hg
      exact hC' n t k hn ht' hk harch hgslab
  obtain ⟨Sg, hS, hSfin', hdecay'⟩ := GAP5

  obtain ⟨C₂, hC₂, hunif⟩ :=
    AdelicEpstein.exists_forall_sub_one_mul_lintegral_nnnorm_sq_mul_epsteinPlus_le_of_decay du Φ M R₀ hR₀ Nf hNf
      hΦM hΦsupp hΦfin 1 2 Φ₀ hΦ₀ GAP2 Sg hS hSfin' u hc haut hdecay'

  have hmass0 : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ) ≠ 0 :=
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos (K := ℚ)).ne'
  have hmassT : NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ) ≠ ⊤ :=
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top (K := ℚ)).ne
  set mass := NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ (AdelicBox.adelicBox ℚ) with hmass_def
  have hD0 : c₂ * mass ^ 3 ≠ 0 := mul_ne_zero hc₂.ne' (pow_ne_zero _ hmass0)
  have hDT : c₂ * mass ^ 3 ≠ ⊤ := ENNReal.mul_ne_top hc₂'.ne (ENNReal.pow_ne_top hmassT)
  set Kc : ℝ≥0∞ := C₁ * C₂ / (c₂ * mass ^ 3) with hKc_def
  have hKcT : Kc ≠ ⊤ := ENNReal.div_ne_top (ENNReal.mul_ne_top hC₁ hC₂) hD0
  refine ⟨Φ, φ₀, hφ₀, hΦwin, Kc.toReal, fun σ hσ => ?_⟩
  have hσ' : σ ∈ Set.Icc (1 : ℝ) 2 := ⟨hσ.1.le, hσ.2⟩
  have hσ1 : 0 < σ - 1 := sub_pos.mpr hσ.1
  have h1 := htorus u hc haut Φ hΦm σ hσ'
  have h2 := hunfold u hu Φ hΦm σ
  have h3 := hunif σ hσ

  have key : ∀ (L Sl Q : ℝ≥0∞), L ≤ C₁ * Q → Sl = c₂ * mass ^ 3 * Q → ENNReal.ofReal (σ - 1) * Sl ≤ C₂ →
      L ≤ ENNReal.ofReal (Kc.toReal / (σ - 1)) := by
    intro L Sl Q hL hSl hr
    have hr0 : ENNReal.ofReal (σ - 1) ≠ 0 := (ENNReal.ofReal_pos.mpr hσ1).ne'
    have hrT : ENNReal.ofReal (σ - 1) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [hSl] at hr

    have hQ : Q ≤ C₂ / (ENNReal.ofReal (σ - 1) * (c₂ * mass ^ 3)) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero hr0 hD0)) (Or.inl (ENNReal.mul_ne_top hrT hDT))]
      calc Q * (ENNReal.ofReal (σ - 1) * (c₂ * mass ^ 3)) = ENNReal.ofReal (σ - 1) * (c₂ * mass ^ 3 * Q) := by ring
        _ ≤ C₂ := hr
    calc L ≤ C₁ * Q := hL
      _ ≤ C₁ * (C₂ / (ENNReal.ofReal (σ - 1) * (c₂ * mass ^ 3))) := by gcongr
      _ = Kc / ENNReal.ofReal (σ - 1) := by
          rw [hKc_def]
          simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hr0) (Or.inl hrT)]
          ring
      _ = ENNReal.ofReal (Kc.toReal / (σ - 1)) := by
          rw [ENNReal.ofReal_div_of_pos hσ1, ENNReal.ofReal_toReal hKcT]
  exact key _ _ _ h1 h2 h3

end S_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_lintegral_torus_whittaker3_sq_le_div_sub_one_of_isCuspidalAlong_of_isRightInvariant (solution)
