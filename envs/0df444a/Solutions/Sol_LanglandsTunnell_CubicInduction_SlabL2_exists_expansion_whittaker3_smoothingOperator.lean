-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.exists_expansion_whittaker3_smoothingOperator
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/de28182a-7853-511d-bce5-b9885dfb9e6e

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_HeightOneSpectrum
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchSmooth3
import Definitions.Def_LanglandsTunnell_CubicInduction_WhittakerBlock
import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous
import Theorems.Thm_LanglandsTunnell_CubicInduction_isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_whittaker3_mul_iotaGL_zpow_eq_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_one_le_and_lintegral_quotientMeasure_eq_mul_whittakerBlock
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_tendsto_sub_one_mul_and_whittakerBlock_one_mul_eq_of_whittakerBlock_le
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_LanglandsTunnell_CubicInduction_isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem
import Theorems.Thm_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
import Theorems.Thm_LanglandsTunnell_CubicInduction_adelicGLHaar_siegelSet_inter_setOf_ideleNorm_det_mem_Icc_lt_top
import Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_pos_lt_top_lintegral_slab_eq_mul_pow_three_mul_lintegral_quotientMeasure
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_isCompactOperator_cuspidalSubspace_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_mul_eq_unipotent_mul_diagonal_mul_compact
import Theorems.Thm_LanglandsTunnell_CubicInduction_isCompact_localMaximalCompact3
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_inner_toL2_translateRight_ne_zero_of_forall_whittakerBlock_one_mul_eq
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b"
p2m_attr_erase "simp" "AutomorphicForm.SmoothCuspRealizationAt.mk.injEq AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.CubicInduction.SlabL2
open scoped InnerProductSpace

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "SlabL2.realCoordinate SlabL2.archEntries SlabL2.IsSmoothArchFactor AdelicGL globalPointsGL centralScalarGL upperUnipotent3 upperUnipotent3_coe radicalP21 radicalP12 radicalP21_coe radicalP12_coe localMaximalCompact3 mem_localMaximalCompact3_iff componentAt3 archComponent3 whittaker3 IsCuspidalAlongP21 IsCuspidalAlongP12 LocalGL3 heckeGen1 heckeGen2 cosetSum IsCosetEigenfunction IsRightInvariant archPlaceComponent3 IsModerateGrowth3 isModerateGrowth3_of_bounded matrixFin_ext matrixAdele_ext localMatN mapMatrix_localMatN_self mapMatrix_localMatN_of_ne finMatN mapMatrix_arch_finMatN mapMatrix_fin_finMatN finEmbedN localToAdelic3 archRoot₁ archRoot₂ exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc exists_isCompactOperator_cuspidalSubspace_smoothingOperator exists_mul_eq_unipotent_mul_diagonal_mul_compact isCompact_localMaximalCompact3 WhittakerBlock.archDeriv"
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

open MeasureTheory
open scoped ENNReal

open Matrix in

private def IsRapidlyDecreasingOnSiegel3 (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ h : AdelicGL 3 (𝓞 ℚ) ℚ, archComponent3 (𝓞 ℚ) ℚ h = 1 →
    ∀ (N : ℕ) (c : ℝ), 0 < c → ∀ C : ℝ, ∃ K : ℝ, ∀ (n t k : AdelicGL 3 (𝓞 ℚ) ℚ)
        (_hx :
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      ∀ w : InfinitePlace ℚ,
        (∀ i j : Fin 3,
          (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
          (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j →
          (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
        (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1),
      ∀ w : InfinitePlace ℚ,
        ‖f (n * t * k * h)‖ ≤ K * ((archRoot₁ ℚ w t * archRoot₂ ℚ w t) ^ N)⁻¹

private def RigidAdm (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  φ ∈ cuspFunctions ω a b Φ₀ ∧
    (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) ∧
    (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) φ (lam1 p)) ∧
    (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) φ (lam2 p)) ∧
    IsRapidlyDecreasingOnSiegel3 φ

private theorem rigidAdm_props (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    ∀ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, RigidAdm S ω lam1 lam2 a b Φ₀ φ →
      Continuous φ ∧
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
        φ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * φ g) ∧
      (∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) φ) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) φ (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) φ (lam2 p)) := by
  intro φ h
  have hm := (mem_automorphicSubmodule_iff ω a b Φ₀ φ).mp h.1.1
  exact ⟨h.1.2.1, hm.1, hm.2.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

section OrthogonalityPropagation

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private theorem secondCountableTopology_adeleRing : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) :=
  NumberField.AdeleRing.secondCountableTopology ℚ

attribute [local instance] secondCountableTopology_adeleRing

private noncomputable abbrev boxMeasure : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

private theorem isProbabilityMeasure_boxMeasure : IsProbabilityMeasure boxMeasure :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

attribute [local instance] isProbabilityMeasure_boxMeasure

private theorem integrable_boxMeasure_of_continuous {u : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) :
    Integrable u boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hC' : IntegrableOn u C (AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) := hu.continuousOn.integrableOn_compact hC
  exact Integrable.smul_measure (hC'.mono_set hsub)
    (ENNReal.inv_ne_top.mpr (AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')

private theorem continuous_integral_boxMeasure {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [LocallyCompactSpace X] {u : X → AdeleRing (𝓞 ℚ) ℚ → ℂ} (hu : Continuous (Function.uncurry u)) :
    Continuous fun t => ∫ y, u t y ∂boxMeasure := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  obtain ⟨N, hN, hNt⟩ := exists_compact_mem_nhds t₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hu.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun t =>
      (hu.comp (f := fun y => (t, y)) (by fun_prop)).aestronglyMeasurable
  · refine Filter.mem_of_superset hNt fun t ht => ?_
    exact (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy =>
      hM (t, y) ⟨ht, hsub hy⟩
  · exact Filter.Eventually.of_forall fun y => (hu.comp (f := fun t => (t, y)) (by fun_prop)).continuousAt

private theorem integral_integral_boxMeasure_add {u u' : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hu : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u q.1 q.2)
    (hu' : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u' q.1 q.2) :
    (∫ x, ∫ y, (u x y + u' x y) ∂boxMeasure ∂boxMeasure) =
      (∫ x, ∫ y, u x y ∂boxMeasure ∂boxMeasure) + ∫ x, ∫ y, u' x y ∂boxMeasure ∂boxMeasure := by
  have hin : ∀ x, (∫ y, (u x y + u' x y) ∂boxMeasure) = (∫ y, u x y ∂boxMeasure) + ∫ y, u' x y ∂boxMeasure :=
    fun x => integral_add (integrable_boxMeasure_of_continuous (hu.comp (f := fun y => (x, y)) (by fun_prop)))
      (integrable_boxMeasure_of_continuous (hu'.comp (f := fun y => (x, y)) (by fun_prop)))
  simp_rw [hin]
  exact integral_add (integrable_boxMeasure_of_continuous (continuous_integral_boxMeasure (u := u) hu))
    (integrable_boxMeasure_of_continuous (continuous_integral_boxMeasure (u := u') hu'))

private theorem upperUnipotent3_inv_coe (x y z : AdeleRing (𝓞 ℚ) ℚ) :
    (((upperUnipotent3 x y z)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      !![1, -x, x * y - z; 0, 1, -y; 0, 0, 1] :=
  rfl

private theorem continuous_upperUnipotent3 :
    Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
      (upperUnipotent3 q.1 q.2.1 q.2.2 : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    simp only [Function.comp_apply, upperUnipotent3_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    simp only [upperUnipotent3_inv_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem continuous_radicalP21_of_pair :
    Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![q.1, q.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 0 q.2 q.1
  exact continuous_upperUnipotent3.comp
    (f := fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => ((0 : AdeleRing (𝓞 ℚ) ℚ), q.2, q.1)) (by fun_prop)

private theorem continuous_radicalP12_of_pair :
    Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![q.1, q.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  show Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => upperUnipotent3 q.1 0 q.2
  exact continuous_upperUnipotent3.comp
    (f := fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (q.1, (0 : AdeleRing (𝓞 ℚ) ℚ), q.2)) (by fun_prop)

private noncomputable abbrev cuspidalPins : CarrierPins ℚ :=
  productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

private theorem isCuspidalAlongP21_add {u u' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) (hu' : Continuous u')
    (h : IsCuspidalAlongP21 cuspidalPins u) (h' : IsCuspidalAlongP21 cuspidalPins u') :
    IsCuspidalAlongP21 cuspidalPins (u + u') := by
  intro g
  have hc : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u (radicalP21 ![q.1, q.2] * g) :=
    hu.comp (continuous_radicalP21_of_pair.mul continuous_const)
  have hc' : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u' (radicalP21 ![q.1, q.2] * g) :=
    hu'.comp (continuous_radicalP21_of_pair.mul continuous_const)
  have e := integral_integral_boxMeasure_add (u := fun x y => u (radicalP21 ![x, y] * g))
    (u' := fun x y => u' (radicalP21 ![x, y] * g)) hc hc'
  simp only [Pi.add_apply]
  exact e.trans ((congrArg₂ (· + ·) (h g) (h' g)).trans (add_zero (0 : ℂ)))

private theorem isCuspidalAlongP12_add {u u' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hu : Continuous u) (hu' : Continuous u')
    (h : IsCuspidalAlongP12 cuspidalPins u) (h' : IsCuspidalAlongP12 cuspidalPins u') :
    IsCuspidalAlongP12 cuspidalPins (u + u') := by
  intro g
  have hc : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u (radicalP12 ![q.1, q.2] * g) :=
    hu.comp (continuous_radicalP12_of_pair.mul continuous_const)
  have hc' : Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u' (radicalP12 ![q.1, q.2] * g) :=
    hu'.comp (continuous_radicalP12_of_pair.mul continuous_const)
  have e := integral_integral_boxMeasure_add (u := fun x y => u (radicalP12 ![x, y] * g))
    (u' := fun x y => u' (radicalP12 ![x, y] * g)) hc hc'
  simp only [Pi.add_apply]
  exact e.trans ((congrArg₂ (· + ·) (h g) (h' g)).trans (add_zero (0 : ℂ)))

private theorem isCuspidalAlongP21_smul (c : ℂ) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (h : IsCuspidalAlongP21 cuspidalPins u) :
    IsCuspidalAlongP21 cuspidalPins (c • u) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, h g, mul_zero]

private theorem isCuspidalAlongP12_smul (c : ℂ) {u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (h : IsCuspidalAlongP12 cuspidalPins u) :
    IsCuspidalAlongP12 cuspidalPins (c • u) := by
  intro g
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, h g, mul_zero]

private theorem add_smul_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {x y : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hx : x ∈ cuspFunctions ω a b Φ₀) (hy : y ∈ cuspFunctions ω a b Φ₀) (c : ℂ) :
    x + c • y ∈ cuspFunctions ω a b Φ₀ :=
  ⟨(automorphicSubmodule ω a b Φ₀).add_mem hx.1 ((automorphicSubmodule ω a b Φ₀).smul_mem c hy.1),
    hx.2.1.add (hy.2.1.const_smul c),
    isCuspidalAlongP21_add hx.2.1 (hy.2.1.const_smul c) hx.2.2.1 (isCuspidalAlongP21_smul c hy.2.2.1),
    isCuspidalAlongP12_add hx.2.1 (hy.2.1.const_smul c) hx.2.2.2 (isCuspidalAlongP12_smul c hy.2.2.2)⟩

private theorem inner_eq_inner_of_forall_norm_add_smul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {X Y X' Y' : E} (h : ∀ c : ℂ, ‖X' + c • Y'‖ = ‖X + c • Y‖) : ⟪X', Y'⟫_ℂ = ⟪X, Y⟫_ℂ := by
  have h₁ : ‖X' + Y'‖ = ‖X + Y‖ := by simpa using h 1
  have h₂ : ‖X' - Y'‖ = ‖X - Y‖ := by simpa [sub_eq_add_neg] using h (-1)
  have h₃ : ‖X' - (RCLike.I : ℂ) • Y'‖ = ‖X - (RCLike.I : ℂ) • Y‖ := by
    simpa [sub_eq_add_neg] using h (-(RCLike.I : ℂ))
  have h₄ : ‖X' + (RCLike.I : ℂ) • Y'‖ = ‖X + (RCLike.I : ℂ) • Y‖ := h (RCLike.I : ℂ)
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four]
  simp only [h₁, h₂, h₃, h₄]

private theorem translateRight_add_smul (v : AdelicGL 3 (𝓞 ℚ) ℚ) (x y : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (c : ℂ) :
    translateRight v (x + c • y) = translateRight v x + c • translateRight v y := by
  funext g
  simp [translateRight]

private theorem toL2_add_smul (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {x y : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hx : x ∈ automorphicSubmodule ω a b Φ₀) (hy : y ∈ automorphicSubmodule ω a b Φ₀)
    (c : ℂ) (hxy : x + c • y ∈ automorphicSubmodule ω a b Φ₀) :
    toL2 ω a b Φ₀ ⟨x + c • y, hxy⟩ = toL2 ω a b Φ₀ ⟨x, hx⟩ + c • toL2 ω a b Φ₀ ⟨y, hy⟩ := by
  have e : (⟨x + c • y, hxy⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = ⟨x, hx⟩ + c • ⟨y, hy⟩ := rfl
  rw [e, map_add, map_smul]

private theorem inner_toL2_translateRight_translateRight (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsSlabDomain a b Φ₀) {x y : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hx : x ∈ cuspFunctions ω a b Φ₀)
    (hy : y ∈ cuspFunctions ω a b Φ₀) (v : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hxv : translateRight v x ∈ automorphicSubmodule ω a b Φ₀)
    (hyv : translateRight v y ∈ automorphicSubmodule ω a b Φ₀) :
    ⟪toL2 ω a b Φ₀ ⟨translateRight v x, hxv⟩, toL2 ω a b Φ₀ ⟨translateRight v y, hyv⟩⟫_ℂ =
      ⟪toL2 ω a b Φ₀ ⟨x, hx.1⟩, toL2 ω a b Φ₀ ⟨y, hy.1⟩⟫_ℂ := by
  refine inner_eq_inner_of_forall_norm_add_smul_eq fun c => ?_
  have hxy : x + c • y ∈ cuspFunctions ω a b Φ₀ := add_smul_mem_cuspFunctions ω a b Φ₀ hx hy c
  obtain ⟨hmem, hnorm, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ (x + c • y) hxy
  have hv : translateRight v (x + c • y) ∈ automorphicSubmodule ω a b Φ₀ := (hmem v).1
  have e : toL2 ω a b Φ₀ ⟨translateRight v (x + c • y), hv⟩ =
      toL2 ω a b Φ₀ ⟨translateRight v x, hxv⟩ + c • toL2 ω a b Φ₀ ⟨translateRight v y, hyv⟩ := by
    have e' : (⟨translateRight v (x + c • y), hv⟩ : ↥(automorphicSubmodule ω a b Φ₀)) =
        ⟨translateRight v x, hxv⟩ + c • ⟨translateRight v y, hyv⟩ :=
      Subtype.ext (translateRight_add_smul v x y c)
    rw [e', map_add, map_smul]
  rw [← e, ← toL2_add_smul ω a b Φ₀ hx.1 hy.1 c hxy.1]
  exact hnorm v

private theorem toL2_congr (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {z z' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hz : z ∈ automorphicSubmodule ω a b Φ₀) (hz' : z' ∈ automorphicSubmodule ω a b Φ₀)
    (e : z = z') : toL2 ω a b Φ₀ ⟨z, hz⟩ = toL2 ω a b Φ₀ ⟨z', hz'⟩ := by
  have h : (⟨z, hz⟩ : automorphicSubmodule ω a b Φ₀) = ⟨z', hz'⟩ := Subtype.ext e
  rw [h]

private theorem translateRight_eq_translateRight_translateRight (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (u w : AdelicGL 3 (𝓞 ℚ) ℚ) : translateRight w F = translateRight u (translateRight (u⁻¹ * w) F) := by
  funext x
  simp only [translateRight_apply, mul_inv_cancel_left, mul_assoc]

private theorem inner_toL2_eq_integral (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (Y : Carrier a b Φ₀) {z : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hz : z ∈ automorphicSubmodule ω a b Φ₀) :
    ⟪Y, toL2 ω a b Φ₀ ⟨z, hz⟩⟫_ℂ = ∫ x, (starRingEnd ℂ) (Y x) * z x ∂(domainMeasure a b Φ₀) := by
  rw [toL2_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hz.2.2] with x hx
  rw [hx, RCLike.inner_apply]
  exact mul_comm _ _

private theorem norm_toL2_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    {z : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hz : z ∈ automorphicSubmodule ω a b Φ₀) :
    ‖toL2 ω a b Φ₀ ⟨z, hz⟩‖ = (eLpNorm z 2 (domainMeasure a b Φ₀)).toReal := by
  rw [toL2_apply, Lp.norm_toLp]

private theorem integral_norm_mul_norm_le {X : Type*} [MeasurableSpace X] {μ : Measure X} {u v : X → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    ∫ x, ‖u x‖ * ‖v x‖ ∂μ ≤ (eLpNorm u 2 μ).toReal * (eLpNorm v 2 μ).toReal := by
  have h22 : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have hu' : MemLp u (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hu
  have hv' : MemLp v (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hv
  refine (integral_mul_norm_le_Lp_mul_Lq h22 hu' hv').trans (le_of_eq ?_)
  rw [hu.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    hv.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  have hnu : 0 ≤ (∫ x, ‖u x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by positivity
  have hnv : 0 ≤ (∫ x, ‖v x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by positivity
  simp only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal hnu, ENNReal.toReal_ofReal hnv, one_div]

private theorem memLp_conj_of_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X} {u : X → ℂ} (hu : MemLp u 2 μ) :
    MemLp (fun x => (starRingEnd ℂ) (u x)) 2 μ :=
  hu.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hu.1)
    (Filter.Eventually.of_forall fun x => by simp)

private theorem adelicMatrix_secondCountableTopology :
    SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))

private theorem adelicGL_secondCountableTopology : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  haveI := adelicMatrix_secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact (Units.isInducing_embedProduct (M := Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))).secondCountableTopology

section KernelSupport

open Matrix

noncomputable section

private theorem coe_componentAt3
    (v : HeightOneSpectrum (𝓞 ℚ))
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((componentAt3 (𝓞 ℚ) ℚ v g : GL (Fin 3) (v.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) =
      ((AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ v).comp (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)).mapMatrix
        (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_archComponent3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((archComponent3 (𝓞 ℚ) ℚ g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
        Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) =
      (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private def archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.of fun i j =>
    ((g i j, (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)

private theorem mapMatrix_arch_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = g := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply]

private theorem mapMatrix_fin_archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (archMat3 g) = 1 := by
  ext i j
  simp [archMat3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleFin_apply]

private theorem archMat3_one : archMat3 1 = 1 :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ (by rw [mapMatrix_arch_archMat3, map_one])
    (by rw [mapMatrix_fin_archMat3, map_one])

private theorem archMat3_mul (g h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :
    archMat3 (g * h) = archMat3 g * archMat3 h :=
  matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ
    (by rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3, mapMatrix_arch_archMat3])
    (by rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mapMatrix_fin_archMat3, mul_one])

private def archToAdelic3 : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ where
  toFun g :=
    { val := archMat3 g
      inv := archMat3 ((g⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))
      val_inv := by rw [← archMat3_mul, Units.mul_inv, archMat3_one]
      inv_val := by rw [← archMat3_mul, Units.inv_mul, archMat3_one] }
  map_one' := Units.ext (by simp only [Units.val_one]; exact archMat3_one)
  map_mul' g h := Units.ext (by simp only [Units.val_mul]; exact archMat3_mul _ _)

private theorem coe_archToAdelic3 (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    ((archToAdelic3 g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      archMat3 (g : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
  rfl

private theorem componentAt3_archToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ v (archToAdelic3 g) = 1 := by
  apply Units.ext
  rw [coe_componentAt3, coe_archToAdelic3, ← RingHom.mapMatrix_comp, RingHom.comp_apply,
    mapMatrix_fin_archMat3, map_one, Units.val_one]

private def archEntries3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Fin 3 → Fin 3 → ℝ :=
  fun i j => SlabL2.realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)

private theorem isReal_of_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

private theorem continuous_realCoordinate : Continuous realCoordinate :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous.comp
    (continuous_apply Rat.infinitePlace)

private def ofRealAdele (r : ℝ) : InfiniteAdeleRing ℚ :=
  show (v : InfinitePlace ℚ) → v.Completion from
    fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm r

private theorem continuous_ofRealAdele : Continuous ofRealAdele :=
  continuous_pi fun v => (InfinitePlace.Completion.isometryEquivRealOfIsReal (isReal_of_rat v)).symm.continuous

private theorem realCoordinate_ofRealAdele (r : ℝ) : realCoordinate (ofRealAdele r) = r :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private theorem ofRealAdele_realCoordinate (x : InfiniteAdeleRing ℚ) : ofRealAdele (realCoordinate x) = x := by
  funext v
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm_apply_apply
    (x Rat.infinitePlace)

private def realCoordinateRingEquiv : InfiniteAdeleRing ℚ ≃+* ℝ where
  toFun := realCoordinate
  invFun := ofRealAdele
  left_inv := ofRealAdele_realCoordinate
  right_inv := realCoordinate_ofRealAdele
  map_mul' := map_mul realCoordinate
  map_add' := map_add realCoordinate

private def realCoordinateHomeomorph : InfiniteAdeleRing ℚ ≃ₜ ℝ where
  toFun := realCoordinate
  invFun := ofRealAdele
  left_inv := ofRealAdele_realCoordinate
  right_inv := realCoordinate_ofRealAdele
  continuous_toFun := continuous_realCoordinate
  continuous_invFun := continuous_ofRealAdele

private theorem realCoordinateHomeomorph_apply (x : InfiniteAdeleRing ℚ) :
    realCoordinateHomeomorph x = realCoordinate x :=
  rfl

private theorem continuous_archEntries3 : Continuous archEntries3 :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_realCoordinate.comp (Units.continuous_val.matrix_elem i j)

private theorem isCompact_preimage_archEntries3 {T : Set (Fin 3 → Fin 3 → ℝ)} (hT : IsCompact T)
    (hTloc : T ⊆ {m | (Matrix.of m).det ≠ 0}) : IsCompact (archEntries3 ⁻¹' T) := by
  haveI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  have hdet : ∀ x : T, IsUnit (Matrix.of x.1).det := fun x => isUnit_iff_ne_zero.mpr (hTloc x.2)
  let φ : ℝ →+* InfiniteAdeleRing ℚ := realCoordinateRingEquiv.symm
  let u : T → GL (Fin 3) ℝ := fun x =>
    ⟨Matrix.of x.1, (Matrix.of x.1)⁻¹, Matrix.mul_nonsing_inv _ (hdet x), Matrix.nonsing_inv_mul _ (hdet x)⟩
  let j : T → GL (Fin 3) (InfiniteAdeleRing ℚ) := fun x => Units.map (RingHom.mapMatrix φ).toMonoidHom (u x)
  have hof : Continuous fun x : T => Matrix.of x.1 := continuous_subtype_val
  have hinv : Continuous fun x : T => (Matrix.of x.1)⁻¹ := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    have hc : ContinuousAt Ring.inverse (Matrix.of x.1).det := by
      simpa using NormedRing.inverse_continuousAt (hdet x).unit
    exact (continuousAt_matrix_inv (Matrix.of x.1) hc).comp (f := fun x : T => Matrix.of x.1) hof.continuousAt
  have hj : Continuous j := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · refine continuous_matrix fun i k => ?_
      exact continuous_ofRealAdele.comp (hof.matrix_elem i k)
    · refine continuous_matrix fun i k => ?_
      exact continuous_ofRealAdele.comp (hinv.matrix_elem i k)
  have hsub : archEntries3 ⁻¹' T ⊆ Set.range j := by
    intro a ha
    refine ⟨⟨archEntries3 a, ha⟩, Units.ext (Matrix.ext fun i k => ?_)⟩
    show ofRealAdele (realCoordinate ((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i k)) = _
    exact ofRealAdele_realCoordinate _
  exact (isCompact_range hj).of_isClosed_subset (hT.isClosed.preimage continuous_archEntries3) hsub

private theorem archEntries_archToAdelic3 (a : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    SlabL2.archEntries (archToAdelic3 a) = archEntries3 a := by
  funext i j
  rfl

private theorem continuous_archToAdelic3 : Continuous archToAdelic3 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      (((a : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : GL (Fin 3) (InfiniteAdeleRing ℚ) =>
      ((((a⁻¹ : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

private theorem continuous_finEmbedN3 : Continuous (finEmbedN (Fin 3) (𝓞 ℚ) ℚ) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        (k : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) : AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (((1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j,
        ((k⁻¹ : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
        AdeleRing (𝓞 ℚ) ℚ)
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

private def finPart3 : AdelicGL 3 (𝓞 ℚ) ℚ →* GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  Matrix.GeneralLinearGroup.map (AdelicLevel.adeleFin (𝓞 ℚ) ℚ)

private theorem coe_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((finPart3 g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem coe_finEmbedN_three (g : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ((finEmbedN (Fin 3) (𝓞 ℚ) ℚ g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      finMatN (Fin 3) (𝓞 ℚ) ℚ (g : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  rfl

private theorem archToAdelic3_archComponent3_mul_finEmbedN_finPart3 (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archToAdelic3 (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (finPart3 g) = g := by
  apply Units.ext
  rw [Units.val_mul, coe_archToAdelic3, coe_finEmbedN_three, coe_archComponent3, coe_finPart3]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, mapMatrix_arch_archMat3, mapMatrix_arch_finMatN, mul_one]
  · rw [map_mul, mapMatrix_fin_archMat3, mapMatrix_fin_finMatN, one_mul]

private theorem continuous_finPart3 : Continuous finPart3 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ =>
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ ((a : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    exact (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ).comp (Units.continuous_val.matrix_elem i j)
  · refine continuous_matrix fun i j => ?_
    show Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ =>
      AdelicLevel.adeleFin (𝓞 ℚ) ℚ (((a⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j)
    exact (AdelicLevel.continuous_adeleFin (𝓞 ℚ) ℚ).comp (Units.continuous_coe_inv.matrix_elem i j)

private theorem archComponent3_finEmbedN_three (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = 1 := by
  apply Units.ext
  rw [coe_archComponent3, coe_finEmbedN_three, mapMatrix_arch_finMatN, Units.val_one]

private theorem archComponent3_mul_finEmbedN (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    archComponent3 (𝓞 ℚ) ℚ (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = archComponent3 (𝓞 ℚ) ℚ y := by
  rw [map_mul, archComponent3_finEmbedN_three, mul_one]

private theorem fst_coe_mul_finEmbedN (y : AdelicGL 3 (𝓞 ℚ) ℚ)
    (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (i j : Fin 3) :
    (((y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      ((y : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 := by
  have h := congrArg
    (fun u : GL (Fin 3) (InfiniteAdeleRing ℚ) => (u : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j)
    (archComponent3_mul_finEmbedN y k)
  simpa only [coe_archComponent3, RingHom.mapMatrix_apply, Matrix.map_apply, AdelicLevel.adeleArch_apply] using h

private abbrev Gf := GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)

private abbrev finLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) : Set Gf :=
  {k | ∀ p, componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) ∈ K' p}

private abbrev adelicLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {x | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}

private theorem adelicLevelSet_eq_preimage
    (e : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ) (fin : AdelicGL 3 (𝓞 ℚ) ℚ →* Gf)
    (hdec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, e (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g) = g)
    (hcompe : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (a : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      componentAt3 (𝓞 ℚ) ℚ p (e a) = 1)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) :
    adelicLevelSet K' = fin ⁻¹' finLevelSet K' := by
  ext g
  have key : ∀ p, componentAt3 (𝓞 ℚ) ℚ p g = componentAt3 (𝓞 ℚ) ℚ p (finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g)) := by
    intro p
    conv_lhs => rw [← hdec g]
    rw [map_mul, hcompe, one_mul]
  exact forall_congr' fun p => by rw [key p]

private theorem support_subset_image
    (e : GL (Fin 3) (InfiniteAdeleRing ℚ) →* AdelicGL 3 (𝓞 ℚ) ℚ) (fin : AdelicGL 3 (𝓞 ℚ) ℚ →* Gf)
    {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p)) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (SlabL2.archEntries g) * (adelicLevelSet K').indicator (fun _ => (1 : ℂ)) g)
    (hdec : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, e (archComponent3 (𝓞 ℚ) ℚ g) * finEmbedN (Fin 3) (𝓞 ℚ) ℚ (fin g) = g)
    (hcompe : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (a : GL (Fin 3) (InfiniteAdeleRing ℚ)),
      componentAt3 (𝓞 ℚ) ℚ p (e a) = 1)
    (harch : ∀ (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : Gf),
      SlabL2.archEntries (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = SlabL2.archEntries y) :
    Function.support φ ⊆
      (fun q : GL (Fin 3) (InfiniteAdeleRing ℚ) × Gf => e q.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ q.2) ''
        ({a | SlabL2.archEntries (e a) ∈ tsupport α} ×ˢ finLevelSet K') := by
  intro g hg
  rw [Function.mem_support, hφ g] at hg
  have h1 : α (SlabL2.archEntries g) ≠ 0 := left_ne_zero_of_mul hg
  have h2 : g ∈ adelicLevelSet K' := by
    by_contra hn
    exact right_ne_zero_of_mul hg (Set.indicator_of_notMem hn _)
  rw [adelicLevelSet_eq_preimage e fin hdec hcompe] at h2
  refine ⟨(archComponent3 (𝓞 ℚ) ℚ g, fin g), ⟨?_, h2⟩, hdec g⟩
  show SlabL2.archEntries (e (archComponent3 (𝓞 ℚ) ℚ g)) ∈ tsupport α
  have : SlabL2.archEntries (e (archComponent3 (𝓞 ℚ) ℚ g)) = SlabL2.archEntries g := by
    conv_rhs => rw [← hdec g]
    exact (harch _ _).symm
  rw [this]
  exact subset_tsupport α (Function.mem_support.mpr h1)

private theorem archEntries_mul_finEmbedN (y : AdelicGL 3 (𝓞 ℚ) ℚ) (k : GL (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    SlabL2.archEntries (y * finEmbedN (Fin 3) (𝓞 ℚ) ℚ k) = SlabL2.archEntries y := by
  funext i j
  simp only [SlabL2.archEntries, fst_coe_mul_finEmbedN]

private theorem continuous_archEntries : Continuous SlabL2.archEntries := by
  have hreal : Continuous SlabL2.realCoordinate := by
    have : (SlabL2.realCoordinate : InfiniteAdeleRing ℚ → ℝ) = realCoordinateHomeomorph := by
      funext x
      exact (realCoordinateHomeomorph_apply x).symm
    rw [this]
    exact realCoordinateHomeomorph.continuous
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hrow : Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ => (a : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i :=
    Matrix.GeneralLinearGroup.continuous_apply (fun a => a) continuous_id i
  exact hreal.comp (continuous_fst.comp ((continuous_apply j).comp hrow))

private theorem isCompact_setOf_archEntries_archToAdelic3_mem_tsupport {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    (hα : SlabL2.IsSmoothArchFactor α) :
    IsCompact {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | SlabL2.archEntries (archToAdelic3 a) ∈ tsupport α} := by
  have : {a : GL (Fin 3) (InfiniteAdeleRing ℚ) | SlabL2.archEntries (archToAdelic3 a) ∈ tsupport α} =
      archEntries3 ⁻¹' tsupport α := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage, archEntries_archToAdelic3]
  rw [this]
  exact isCompact_preimage_archEntries3 hα.2.1 hα.2.2

end

end KernelSupport

private theorem isOpen_adelicLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) : IsOpen (adelicLevelSet K') := by
  rw [adelicLevelSet_eq_preimage archToAdelic3 finPart3 archToAdelic3_archComponent3_mul_finEmbedN_finPart3
    componentAt3_archToAdelic3 K']
  exact (isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcpt hcof).1.preimage
    continuous_finPart3

private theorem isClosed_adelicLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) : IsClosed (adelicLevelSet K') := by
  rw [adelicLevelSet_eq_preimage archToAdelic3 finPart3 archToAdelic3_archComponent3_mul_finEmbedN_finPart3
    componentAt3_archToAdelic3 K']
  exact (isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' hopen hcpt hcof).2.isClosed.preimage
    continuous_finPart3

private theorem continuous_indicator_adelicLevelSet (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (LocalGL3 p))
    (hopen : ∀ p, IsOpen (K' p : Set (LocalGL3 p))) (hcpt : ∀ p, IsCompact (K' p : Set (LocalGL3 p)))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    Continuous ((adelicLevelSet K').indicator fun _ => (1 : ℂ)) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  by_cases hx : x ∈ adelicLevelSet K'
  · refine (continuousAt_const (y := (1 : ℂ))).congr ?_
    filter_upwards [(isOpen_adelicLevelSet K' hopen hcpt hcof).mem_nhds hx] with y hy
    simp [hy]
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [(isClosed_adelicLevelSet K' hopen hcpt hcof).isOpen_compl.mem_nhds hx] with y hy
    have hy' : y ∉ adelicLevelSet K' := hy
    simp [hy']

private theorem continuous_and_hasCompactSupport_of_isSmoothingKernel {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsSmoothingKernel φ) : Continuous φ ∧ HasCompactSupport φ := by
  obtain ⟨α, K', hα, hoc, hcof, hφeq⟩ := hφ
  have hU := isOpen_and_isCompact_setOf_forall_componentAt3_finEmbedN_mem K' (fun p => (hoc p).1)
    (fun p => (hoc p).2) hcof
  refine ⟨?_, ?_⟩
  · have hφ' : φ = fun g => α (SlabL2.archEntries g) * (adelicLevelSet K').indicator (fun _ => (1 : ℂ)) g :=
      funext hφeq
    rw [hφ']
    exact (hα.1.continuous.comp continuous_archEntries).mul
      (continuous_indicator_adelicLevelSet K' (fun p => (hoc p).1) (fun p => (hoc p).2) hcof)
  · have hC : IsCompact ((fun q : GL (Fin 3) (InfiniteAdeleRing ℚ) × Gf =>
        archToAdelic3 q.1 * finEmbedN (Fin 3) (𝓞 ℚ) ℚ q.2) ''
          ({a | SlabL2.archEntries (archToAdelic3 a) ∈ tsupport α} ×ˢ finLevelSet K')) :=
      ((isCompact_setOf_archEntries_archToAdelic3_mem_tsupport hα).prod hU.2).image
        ((continuous_archToAdelic3.comp continuous_fst).mul (continuous_finEmbedN3.comp continuous_snd))
    have hsub := support_subset_image archToAdelic3 finPart3 K' hφeq
      archToAdelic3_archComponent3_mul_finEmbedN_finPart3 componentAt3_archToAdelic3 archEntries_mul_finEmbedN
    refine HasCompactSupport.intro hC fun x hx => ?_
    by_contra h
    exact hx (hsub h)

private theorem integrable_of_isSmoothingKernel {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) :
    Integrable φ (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
  (continuous_and_hasCompactSupport_of_isSmoothingKernel hφ).1.integrable_of_hasCompactSupport
    (continuous_and_hasCompactSupport_of_isSmoothingKernel hφ).2

private theorem inner_toL2_translateRight_smoothingOperator (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsSlabDomain a b Φ₀) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : Integrable φ (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (hFm : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight k F ∈ automorphicSubmodule ω a b Φ₀) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (hg : translateRight g (smoothingOperator φ F) ∈ automorphicSubmodule ω a b Φ₀) (Y : Carrier a b Φ₀) :
    ⟪Y, toL2 ω a b Φ₀ ⟨translateRight g (smoothingOperator φ F), hg⟩⟫_ℂ =
      ∫ k, φ k * ⟪Y, toL2 ω a b Φ₀ ⟨translateRight (g * k) F, hFm (g * k)⟩⟫_ℂ
        ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  haveI : SFinite (domainMeasure a b Φ₀) := by
    rw [domainMeasure_def, slabMeasure_def]
    infer_instance
  set μ := domainMeasure a b Φ₀ with hμ
  set η := AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hη
  obtain ⟨hmem, hnorm, -⟩ := exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF
  haveI : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) := adelicGL_secondCountableTopology

  set f : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
    fun x k => (starRingEnd ℂ) (Y x) * (φ k * F (x * (g * k))) with hf
  have hYm : MemLp (fun x => (starRingEnd ℂ) (Y x)) 2 μ := memLp_conj_of_memLp (Lp.memLp Y)
  have hWm : ∀ k, MemLp (fun x => F (x * (g * k))) 2 μ := fun k => (hFm (g * k)).2.2

  have hfm : AEStronglyMeasurable (Function.uncurry f) (μ.prod η) := by
    have h1 : AEStronglyMeasurable (fun z : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => (starRingEnd ℂ) (Y z.1))
        (μ.prod η) :=
      Complex.continuous_conj.comp_aestronglyMeasurable
        ((Lp.aestronglyMeasurable Y).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
    have h2 : AEStronglyMeasurable (fun z : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => φ z.2) (μ.prod η) :=
      hφ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have h3 : AEStronglyMeasurable
        (fun z : AdelicGL 3 (𝓞 ℚ) ℚ × AdelicGL 3 (𝓞 ℚ) ℚ => F (z.1 * (g * z.2))) (μ.prod η) :=
      (hF.2.1.comp (continuous_fst.mul (continuous_const.mul continuous_snd))).aestronglyMeasurable
    exact h1.mul (h2.mul h3)

  have hslice : ∀ k, Integrable (fun x => f x k) μ := fun k => by
    have h := (hYm.integrable_mul (hWm k)).const_mul (φ k)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf, Pi.mul_apply]
    ring
  have hbound : ∀ k, ∫ x, ‖f x k‖ ∂μ ≤ ‖φ k‖ * (‖Y‖ * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖) := fun k => by
    have hk : ∫ x, ‖f x k‖ ∂μ = ‖φ k‖ * ∫ x, ‖(starRingEnd ℂ) (Y x)‖ * ‖F (x * (g * k))‖ ∂μ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hf, norm_mul]
      ring
    rw [hk]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (integral_norm_mul_norm_le hYm (hWm k)).trans (le_of_eq ?_)
    have e1 : (eLpNorm (fun x => (starRingEnd ℂ) (Y x)) 2 μ).toReal = ‖Y‖ := by
      rw [Lp.norm_def]
      congr 1
      exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => by simp)
    have e2 : (eLpNorm (fun x => F (x * (g * k))) 2 μ).toReal = ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ := by
      rw [← hnorm (g * k), norm_toL2_eq]
      rfl
    rw [e1, e2]
  have hint : Integrable (Function.uncurry f) (μ.prod η) := by
    refine (integrable_prod_iff' hfm).2 ⟨Filter.Eventually.of_forall fun k => hslice k, ?_⟩
    refine Integrable.mono' ((hφ.norm.mul_const (‖Y‖ * ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖))) ?_
      (Filter.Eventually.of_forall fun k => ?_)
    · exact hfm.norm.prod_swap.integral_prod_right'
    · rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      exact hbound k

  have hL : ⟪Y, toL2 ω a b Φ₀ ⟨translateRight g (smoothingOperator φ F), hg⟩⟫_ℂ = ∫ x, ∫ k, f x k ∂η ∂μ := by
    rw [inner_toL2_eq_integral]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [translateRight_apply, smoothingOperator_apply, hf, mul_assoc]
    rw [integral_const_mul]
  have hR : (∫ k, φ k * ⟪Y, toL2 ω a b Φ₀ ⟨translateRight (g * k) F, hFm (g * k)⟩⟫_ℂ ∂η) =
      ∫ k, ∫ x, f x k ∂μ ∂η := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [inner_toL2_eq_integral, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hf, translateRight_apply]
    ring
  rw [hL, hR]
  exact integral_integral_swap hint

private theorem add_mul_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    (hF' : F' ∈ cuspFunctions ω a b Φ₀) (c : ℂ) :
    (fun x => F x + c * F' x) ∈ cuspFunctions ω a b Φ₀ := by
  exact add_smul_mem_cuspFunctions ω a b Φ₀ hF hF' c

private theorem rigid_step0_twoSided
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ' : IsSmoothingKernel φ')
    (h : ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g (smoothingOperator φ F) ∈ automorphicSubmodule ω a b Φ₀)
      (g' : AdelicGL 3 (𝓞 ℚ) ℚ) (hg' : translateRight g' (smoothingOperator φ' F') ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g (smoothingOperator φ F), hg⟩,
        toL2 ω a b Φ₀ ⟨translateRight g' (smoothingOperator φ' F'), hg'⟩⟫_ℂ ≠ 0) :
    ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ ≠ 0 := by
  obtain ⟨g, hg, g', hg', hne⟩ := h
  obtain ⟨hmem, -, -⟩ := exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF
  obtain ⟨hmem', -, -⟩ := exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F' hF'
  by_contra hcon
  apply hne
  rw [inner_toL2_translateRight_smoothingOperator ω hω a b Φ₀ hΦ₀ (integrable_of_isSmoothingKernel hφ') hF'
    (fun v => (hmem' v).1) g' hg']
  have h0 : ∀ k, ⟪toL2 ω a b Φ₀ ⟨translateRight g (smoothingOperator φ F), hg⟩,
      toL2 ω a b Φ₀ ⟨translateRight (g' * k) F', (hmem' (g' * k)).1⟩⟫_ℂ = 0 := fun k => by
    rw [← inner_conj_symm, inner_toL2_translateRight_smoothingOperator ω hω a b Φ₀ hΦ₀
      (integrable_of_isSmoothingKernel hφ) hF (fun v => (hmem v).1) g hg]
    have h1 : ∀ j, ⟪toL2 ω a b Φ₀ ⟨translateRight (g' * k) F', (hmem' (g' * k)).1⟩,
        toL2 ω a b Φ₀ ⟨translateRight (g * j) F, (hmem (g * j)).1⟩⟫_ℂ = 0 := fun j => by
      rw [← inner_conj_symm]
      have e := translateRight_eq_translateRight_translateRight F (g' * k) (g * j)
      rw [toL2_congr ω a b Φ₀ (hmem (g * j)).1 (e ▸ (hmem (g * j)).1) e,
        inner_toL2_translateRight_translateRight ω hω a b Φ₀ hΦ₀ (hmem ((g' * k)⁻¹ * (g * j))) hF' (g' * k)]
      have h2 : ⟪toL2 ω a b Φ₀ ⟨translateRight ((g' * k)⁻¹ * (g * j)) F, (hmem ((g' * k)⁻¹ * (g * j))).1⟩,
          toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 := by
        by_contra h2
        exact hcon ⟨(g' * k)⁻¹ * (g * j), (hmem ((g' * k)⁻¹ * (g * j))).1, h2⟩
      rw [h2, map_zero]
    simp only [h1, mul_zero, integral_zero, map_zero]
  simp only [h0, mul_zero, integral_zero]

private theorem rigid_step0 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    (F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF' : F' ∈ cuspFunctions ω a b Φ₀)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (h : ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g (smoothingOperator φ F) ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g (smoothingOperator φ F), hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ ≠ 0) :
    ∃ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (hg : translateRight g F ∈ automorphicSubmodule ω a b Φ₀),
      ⟪toL2 ω a b Φ₀ ⟨translateRight g F, hg⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ ≠ 0 := by
  obtain ⟨g, hg, hne⟩ := h
  obtain ⟨hmem, -, -⟩ := exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF
  by_contra hcon
  apply hne
  rw [← inner_conj_symm, inner_toL2_translateRight_smoothingOperator ω hω a b Φ₀ hΦ₀
    (integrable_of_isSmoothingKernel hφ) hF (fun v => (hmem v).1) g hg]
  have h0 : ∀ k, ⟪toL2 ω a b Φ₀ ⟨F', hF'.1⟩,
      toL2 ω a b Φ₀ ⟨translateRight (g * k) F, (hmem (g * k)).1⟩⟫_ℂ = 0 := fun k => by
    rw [← inner_conj_symm]
    have h1 : ⟪toL2 ω a b Φ₀ ⟨translateRight (g * k) F, (hmem (g * k)).1⟩, toL2 ω a b Φ₀ ⟨F', hF'.1⟩⟫_ℂ = 0 := by
      by_contra h1
      exact hcon ⟨g * k, (hmem (g * k)).1, h1⟩
    rw [h1, map_zero]
  simp only [h0, mul_zero, integral_zero, map_zero]

end OrthogonalityPropagation

section InjectivityBridge

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private theorem ideleNorm_det_centralScalarGL_mul_eq (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) =
      TateGlobal.ideleNorm ℚ z ^ 3 * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, TateGlobal.ideleNorm_mul]
  congr 1
  change TateGlobal.ideleNorm ℚ
      (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) z)) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  simp only [TateGlobal.ideleNorm, map_pow, NNReal.coe_pow]

private theorem countable_generalLinearGroup_rat : Countable (Matrix.GeneralLinearGroup (Fin 3) ℚ) := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℚ) := Countable.of_equiv _ Matrix.of
  exact Function.Injective.countable Units.val_injective

private theorem eq_of_toL2_eq (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    {F F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ automorphicSubmodule ω a b Φ₀) (hFco : Continuous F)
    (hF' : F' ∈ automorphicSubmodule ω a b Φ₀) (hF'co : Continuous F')
    (h : toL2 ω a b Φ₀ ⟨F, hF⟩ = toL2 ω a b Φ₀ ⟨F', hF'⟩) : F = F' := by
  obtain ⟨hFl, hFc, -⟩ := (mem_automorphicSubmodule_iff ω a b Φ₀ F).1 hF
  obtain ⟨hF'l, hF'c, -⟩ := (mem_automorphicSubmodule_iff ω a b Φ₀ F').1 hF'

  have hae : ∀ᵐ x ∂(slabMeasure a b), x ∈ Φ₀ → F x = F' x := by
    refine ae_imp_of_ae_restrict ?_
    rw [← domainMeasure_def]
    rw [toL2_apply, toL2_apply] at h
    exact (MemLp.toLp_eq_toLp_iff _ _).mp h

  have hmp : ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ,
      MeasurePreserving (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => globalPointsGL 3 (𝓞 ℚ) ℚ γ * g)
        (slabMeasure a b) (slabMeasure a b) := fun γ => by
    rw [slabMeasure_def]
    exact
      measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc a b γ
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 3) ℚ) := countable_generalLinearGroup_rat
  have hγ : ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ, ∀ᵐ x ∂(slabMeasure a b),
      globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Φ₀ →
        F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * x) = F' (globalPointsGL 3 (𝓞 ℚ) ℚ γ * x) :=
    fun γ => (hmp γ).quasiMeasurePreserving.ae hae
  have hall : ∀ᵐ x ∂(slabMeasure a b), ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ,
      globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Φ₀ →
        F (globalPointsGL 3 (𝓞 ℚ) ℚ γ * x) = F' (globalPointsGL 3 (𝓞 ℚ) ℚ γ * x) :=
    ae_all_iff.2 hγ

  have hslab : ∀ᵐ x ∂(slabMeasure a b), F x = F' x := by
    filter_upwards [hall, hΦ₀.isFundamentalDomain.ae_covers] with x hx hcov
    obtain ⟨⟨γ', γ, rfl⟩, hγx⟩ := hcov
    have hmem : globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Φ₀ := hγx
    have hγeq := hx γ hmem
    rwa [hFl γ x, hF'l γ x] at hγeq

  have hWo : IsOpen {x : AdelicGL 3 (𝓞 ℚ) ℚ | F x ≠ F' x} := isOpen_ne_fun hFco hF'co
  have hWm : MeasurableSet {x : AdelicGL 3 (𝓞 ℚ) ℚ | F x ≠ F' x} := hWo.measurableSet
  have hW0 : slabMeasure a b {x | F x ≠ F' x} = 0 := ae_iff.1 hslab
  rw [slabMeasure_def, Measure.restrict_apply hWm] at hW0

  have hT : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
      AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
        ({x | F x ≠ F' x} ∩ {x | centralScalarGL 3 (𝓞 ℚ) ℚ z * x ∈ ideleNormDetSlab a b}) = 0 := by
    intro z
    refine measure_mono_null (t := (fun x => centralScalarGL 3 (𝓞 ℚ) ℚ z * x) ⁻¹'
      ({x | F x ≠ F' x} ∩ ideleNormDetSlab a b)) ?_ ?_
    · rintro x ⟨hx, hxz⟩
      rw [Set.mem_preimage]
      refine Set.mem_inter ?_ hxz
      show F (centralScalarGL 3 (𝓞 ℚ) ℚ z * x) ≠ F' (centralScalarGL 3 (𝓞 ℚ) ℚ z * x)
      rw [hFc z x, hF'c z x]
      exact fun hzx => hx (mul_left_cancel₀ (ω z).ne_zero hzx)
    · rw [measure_preimage_mul]
      exact hW0

  have ha : 0 < a := hΦ₀.pos
  have hab : a < b := hΦ₀.lt
  have hb : 0 < b := ha.trans hab
  have hq1 : 1 < b / a := (one_lt_div ha).2 hab
  have hq0 : 0 < b / a := one_pos.trans hq1
  choose z hz using fun n : ℤ => TateGlobal.exists_ideleNorm_eq_and_snd_eq_one ℚ (((b / a) ^ n) ^ (1 / 3 : ℝ))
    (Real.rpow_pos_of_pos (zpow_pos hq0 n) _)
  have hz3 : ∀ n : ℤ, TateGlobal.ideleNorm ℚ (z n) ^ 3 = (b / a) ^ n := fun n => by
    rw [(hz n).2, ← Real.rpow_natCast, ← Real.rpow_mul (zpow_pos hq0 n).le]
    norm_num
  have hcover : {x : AdelicGL 3 (𝓞 ℚ) ℚ | F x ≠ F' x} ⊆
      ⋃ n : ℤ, {x | F x ≠ F' x} ∩ {x | centralScalarGL 3 (𝓞 ℚ) ℚ (z n) * x ∈ ideleNormDetSlab a b} := by
    intro x hx
    have hs : 0 < TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) := TateGlobal.ideleNorm_pos _
    obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow (div_pos ha hs) hq1
    refine Set.mem_iUnion.2 ⟨m + 1, Set.mem_inter hx ?_⟩
    show centralScalarGL 3 (𝓞 ℚ) ℚ (z (m + 1)) * x ∈ ideleNormDetSlab a b
    rw [mem_ideleNormDetSlab_iff, ideleNorm_det_centralScalarGL_mul_eq, hz3, Set.mem_Icc]
    constructor
    · exact ((div_lt_iff₀ hs).1 hm2).le
    · rw [zpow_add_one₀ hq0.ne', mul_comm ((b / a) ^ m) (b / a), mul_assoc]
      calc b / a * ((b / a) ^ m * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x))
          ≤ b / a * (a / TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x) *
              TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det x)) := by gcongr
        _ = b := by rw [div_mul_cancel₀ a hs.ne', div_mul_cancel₀ b ha.ne']

  have hnull : AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ {x | F x ≠ F' x} = 0 :=
    measure_mono_null hcover (measure_iUnion_null fun n => hT (z n))
  have hempty : {x : AdelicGL 3 (𝓞 ℚ) ℚ | F x ≠ F' x} = ∅ :=
    (hWo.measure_eq_zero_iff (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)).1 hnull
  funext x
  by_contra hx
  have hxW : x ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | F x ≠ F' x} := hx
  rw [hempty] at hxW
  exact hxW

private theorem toL2_ne_zero_of_ne_zero (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsSlabDomain a b Φ₀) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀) (hF0 : F ≠ 0) :
    toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0 := by
  have _ := hω
  intro h0
  apply hF0
  have hz : toL2 ω a b Φ₀ ⟨0, (automorphicSubmodule ω a b Φ₀).zero_mem⟩ = 0 := map_zero _
  exact eq_of_toL2_eq ω a b Φ₀ hΦ₀ hF.1 hF.2.1 (automorphicSubmodule ω a b Φ₀).zero_mem continuous_zero
    (h0.trans hz.symm)

end InjectivityBridge

section TranslateCombinationClosure

private theorem fin_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) := by
  change (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
    (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) _))) = _
  rw [mapMatrix_fin_finMatN]

private theorem arch_localToAdelic3 (p : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 p) :
    (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (localToAdelic3 p x : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      1 := by
  change (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (finMatN (Fin 3) (𝓞 ℚ) ℚ
    (localMatN (Fin 3) (𝓞 ℚ) ℚ p (x : Matrix (Fin 3) (Fin 3) _))) = _
  rw [mapMatrix_arch_finMatN]

private theorem componentAt3_coe {q : HeightOneSpectrum (𝓞 ℚ)} (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    (componentAt3 (𝓞 ℚ) ℚ q g : Matrix (Fin 3) (Fin 3) (q.adicCompletion ℚ)) =
      (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ q).mapMatrix
        ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) :=
  rfl

private theorem mul_localToAdelic3_comm_of_componentAt3_eq_one {p : HeightOneSpectrum (𝓞 ℚ)} {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : componentAt3 (𝓞 ℚ) ℚ p g = 1) (x : LocalGL3 p) :
    g * localToAdelic3 p x = localToAdelic3 p x * g := by
  have hg' : (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix
      ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) = 1 := by
    rw [← componentAt3_coe, hg, Units.val_one]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  refine matrixAdele_ext (Fin 3) (𝓞 ℚ) ℚ ?_ ?_
  · rw [map_mul, map_mul, arch_localToAdelic3 p, mul_one, one_mul]
  · rw [map_mul, map_mul, fin_localToAdelic3 p]
    refine matrixFin_ext (Fin 3) (𝓞 ℚ) ℚ fun w => ?_
    by_cases hw : w = p
    · subst hw
      rw [map_mul, map_mul, hg', mapMatrix_localMatN_self, one_mul, mul_one]
    · rw [map_mul, map_mul, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hw, one_mul, mul_one]

private theorem exists_eq_localToAdelic3_of_mem_doubleCoset {p : HeightOneSpectrum (𝓞 ℚ)} {gen : LocalGL3 p}
    {r : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hr : r ∈ HeckePair.doubleCoset ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p gen)) :
    ∃ y : LocalGL3 p, r = localToAdelic3 p y := by
  obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hr
  obtain ⟨k₁, -, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨k₂, -, rfl⟩ := Subgroup.mem_map.mp hv
  exact ⟨k₁ * gen * k₂, by rw [map_mul, map_mul]⟩

private theorem isCosetEigenfunction_sum_translate {p : HeightOneSpectrum (𝓞 ℚ)} {gen : LocalGL3 p} {lam : ℂ}
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} {n : ℕ} {c : Fin n → ℂ} {t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ}
    (ht : ∀ i, componentAt3 (𝓞 ℚ) ℚ p (t i) = 1)
    (hf : IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p gen) f lam) :
    IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (localToAdelic3 p gen)
      (fun x => ∑ i, c i * f (x * t i)) lam := by
  intro ι _ reps hreps x
  have hcomm : ∀ j i, x * reps j * t i = x * t i * reps j := by
    intro j i
    obtain ⟨y, hy⟩ := exists_eq_localToAdelic3_of_mem_doubleCoset (hreps.mem_doubleCoset j)
    rw [hy, mul_assoc, ← mul_localToAdelic3_comm_of_componentAt3_eq_one (ht i) y, ← mul_assoc]
  simp only [cosetSum] at hf ⊢
  calc (∑ j, ∑ i, c i * f (x * reps j * t i))
      = ∑ i, c i * ∑ j, f (x * t i * reps j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hcomm]
    _ = ∑ i, c i * (lam * f (x * t i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have h := hf ι reps hreps (x * t i)
        simp only [cosetSum] at h
        rw [h]
    _ = lam * ∑ i, c i * f (x * t i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

private theorem sum_mul_mem_cuspFunctions (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {f₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf₀ : f₀ ∈ cuspFunctions ω a b Φ₀) :
    ∀ (m : ℕ) (c : Fin m → ℂ) (F : Fin m → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ), (∀ i, F i ∈ cuspFunctions ω a b Φ₀) →
      (fun x => ∑ i, c i * F i x) ∈ cuspFunctions ω a b Φ₀
  | 0, c, F, _ => by
    have h := add_mul_mem_cuspFunctions ω a b Φ₀ f₀ f₀ hf₀ hf₀ (-1)
    have hfun : (fun x => ∑ i : Fin 0, c i * F i x) = fun x => f₀ x + (-1) * f₀ x := by
      funext x
      simp
    rw [hfun]
    exact h
  | m + 1, c, F, hF => by
    have ih := sum_mul_mem_cuspFunctions ω a b Φ₀ hf₀ m (fun i => c i.castSucc) (fun i => F i.castSucc)
      fun i => hF i.castSucc
    have h := add_mul_mem_cuspFunctions ω a b Φ₀ _ _ ih (hF (Fin.last m)) (c (Fin.last m))
    have hfun : (fun x => ∑ i, c i * F i x) =
        fun x => (∑ i : Fin m, c i.castSucc * F i.castSucc x) + c (Fin.last m) * F (Fin.last m) x := by
      funext x
      exact Fin.sum_univ_castSucc fun i => c i * F i x
    rw [hfun]
    exact h

private theorem isRapidlyDecreasingOnSiegel3_sum_translate {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hf : IsRapidlyDecreasingOnSiegel3 f) {n : ℕ} (c : Fin n → ℂ) {t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ}
    (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    IsRapidlyDecreasingOnSiegel3 fun x => ∑ i, c i * f (x * t i) := by
  intro h hh N d hd C
  have hK := fun i => hf (h * t i) (by rw [map_mul, hh, ht i, one_mul]) N d hd C
  choose K hK using hK
  refine ⟨∑ i, ‖c i‖ * K i, fun n' t' k hx w => ?_⟩
  simp only
  calc ‖∑ i, c i * f (n' * t' * k * h * t i)‖
      ≤ ∑ i, ‖c i * f (n' * t' * k * h * t i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * (K i * ((archRoot₁ ℚ w t' * archRoot₂ ℚ w t') ^ N)⁻¹) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, mul_assoc (n' * t' * k) h (t i)]
        exact mul_le_mul_of_nonneg_left (hK i n' t' k hx w) (norm_nonneg _)
    _ = (∑ i, ‖c i‖ * K i) * ((archRoot₁ ℚ w t' * archRoot₂ ℚ w t') ^ N)⁻¹ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

private theorem rigid_hadm₀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hf : RigidAdm S ω lam1 lam2 a b Φ₀ f) :
    ∀ (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ),
      (∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1 ∧
        ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → componentAt3 (𝓞 ℚ) ℚ p (t i) = 1) →
      RigidAdm S ω lam1 lam2 a b Φ₀ (fun x => ∑ i, c i * f (x * t i)) := by
  intro n c t ht
  obtain ⟨hmem, -, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ f hf.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    exact sum_mul_mem_cuspFunctions ω a b Φ₀ hf.1 n c (fun i => translateRight (t i) f) fun i => hmem (t i)
  ·
    intro p hp x u hu
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hu
    simp only
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← mul_localToAdelic3_comm_of_componentAt3_eq_one ((ht i).2 p hp) k, ← mul_assoc,
      hf.2.1 p hp (x * t i) _ (Subgroup.mem_map_of_mem _ hk)]
  ·
    intro p hp
    exact isCosetEigenfunction_sum_translate (fun i => (ht i).2 p hp) (hf.2.2.1 p hp)
  ·
    intro p hp
    exact isCosetEigenfunction_sum_translate (fun i => (ht i).2 p hp) (hf.2.2.2.1 p hp)
  ·
    exact isRapidlyDecreasingOnSiegel3_sum_translate hf.2.2.2.2 c fun i => (ht i).1

end TranslateCombinationClosure

section SmoothedMember

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] secondCountableTopology_adeleRing

section KernelSupport

open Matrix

noncomputable section

end

end KernelSupport

private noncomputable def archEntriesHom : AdeleRing (𝓞 ℚ) ℚ →+* ℝ := realCoordinate.comp (RingHom.fst _ _)

private theorem archEntries_eq (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.of (archEntries g) = archEntriesHom.mapMatrix (g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) := by
  ext i j
  rfl

private theorem archEntries_mul (x y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.of (archEntries (x * y)) = Matrix.of (archEntries x) * Matrix.of (archEntries y) := by
  rw [archEntries_eq, archEntries_eq, archEntries_eq, Units.val_mul, map_mul]

private theorem of_archEntries_eq_one {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    Matrix.of (archEntries h) = 1 := by
  have hmat : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    change ((archComponent3 (𝓞 ℚ) ℚ h : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
      Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1
    rw [hh, Units.val_one]
  ext i j
  have hij := congrFun (congrFun hmat i) j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply] at hij
  rw [archEntries_eq, RingHom.mapMatrix_apply, Matrix.map_apply]
  change realCoordinate (((h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1) = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
  have h1 : ((h : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j := hij
  rw [h1]
  rcases eq_or_ne i j with rfl | hne
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hne, Matrix.one_apply_ne hne, map_zero]

private theorem archEntries_conj_eq {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) : archEntries (h⁻¹ * g * h) = archEntries g := by
  have h1 : Matrix.of (archEntries h) = 1 := of_archEntries_eq_one hh
  have h2 : Matrix.of (archEntries h⁻¹) = 1 := of_archEntries_eq_one (by rw [map_inv, hh, inv_one])
  have h3 := archEntries_mul (h⁻¹ * g) h
  rw [archEntries_mul h⁻¹ g, h1, h2, one_mul, mul_one] at h3
  exact Matrix.of.injective h3

private theorem eventually_componentAt3_mem_localMaximalCompact3 (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∀ᶠ p in Filter.cofinite, componentAt3 (𝓞 ℚ) ℚ p h ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p := by
  have hint : ∀ (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3), ∀ᶠ p in Filter.cofinite,
      Valued.v (((componentAt3 (𝓞 ℚ) ℚ p g : GL (Fin 3) (p.adicCompletion ℚ)) :
        Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1 := by
    intro g i j
    filter_upwards [(((g : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2).eventually] with p hp
    exact hp
  have hh := Filter.eventually_all.2 fun ij : Fin 3 × Fin 3 => hint h ij.1 ij.2
  have hh' := Filter.eventually_all.2 fun ij : Fin 3 × Fin 3 => hint h⁻¹ ij.1 ij.2
  filter_upwards [hh, hh'] with p hp hp'
  rw [mem_localMaximalCompact3_iff]
  refine ⟨fun i j => hp (i, j), fun i j => ?_⟩
  rw [← map_inv]
  exact hp' (i, j)

private theorem isSmoothingKernel_conj {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ)
    {h : AdelicGL 3 (𝓞 ℚ) ℚ} (hh : archComponent3 (𝓞 ℚ) ℚ h = 1) :
    IsSmoothingKernel fun k => φ (h⁻¹ * k * h) := by
  obtain ⟨α, K', hα, hK', hcof, hφ⟩ := hφ
  refine ⟨α, fun p => (K' p).map (MulAut.conj (componentAt3 (𝓞 ℚ) ℚ p h)).toMonoidHom, hα, ?_, ?_, ?_⟩
  · intro p
    have hco : Continuous fun y : GL (Fin 3) (p.adicCompletion ℚ) =>
        componentAt3 (𝓞 ℚ) ℚ p h * y * (componentAt3 (𝓞 ℚ) ℚ p h)⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hco' : Continuous fun y : GL (Fin 3) (p.adicCompletion ℚ) =>
        (componentAt3 (𝓞 ℚ) ℚ p h)⁻¹ * y * componentAt3 (𝓞 ℚ) ℚ p h :=
      (continuous_const.mul continuous_id).mul continuous_const
    constructor
    · have hset : ((K' p).map (MulAut.conj (componentAt3 (𝓞 ℚ) ℚ p h)).toMonoidHom :
          Set (GL (Fin 3) (p.adicCompletion ℚ))) =
          (fun y => (componentAt3 (𝓞 ℚ) ℚ p h)⁻¹ * y * componentAt3 (𝓞 ℚ) ℚ p h) ⁻¹'
            (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) := by
        ext y
        simp only [SetLike.mem_coe, Set.mem_preimage, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      rw [hset]
      exact (hK' p).1.preimage hco'
    · rw [Subgroup.coe_map]
      exact (hK' p).2.image hco
  · filter_upwards [hcof, eventually_componentAt3_mem_localMaximalCompact3 h] with p hp hmem
    rw [hp]
    ext y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    constructor
    · intro hy
      have hy' := Subgroup.mul_mem _ (Subgroup.mul_mem _ hmem hy) (Subgroup.inv_mem _ hmem)
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] at hy'
      exact hy'
    · intro hy
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmem) hy) hmem
  · intro g
    have hiff : (h⁻¹ * g * h ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}) ↔
        g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ |
          ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ (K' p).map (MulAut.conj (componentAt3 (𝓞 ℚ) ℚ p h)).toMonoidHom} := by
      simp only [Set.mem_setOf_eq, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, map_mul, map_inv]
    show φ (h⁻¹ * g * h) = _
    rw [hφ (h⁻¹ * g * h), archEntries_conj_eq hh g]
    by_cases hg : g ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ |
        ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ (K' p).map (MulAut.conj (componentAt3 (𝓞 ℚ) ℚ p h)).toMonoidHom}
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hiff.2 hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h' => hg (hiff.1 h'))]

private theorem _root_.LanglandsTunnell.CubicInduction.continuous_conj (h : AdelicGL 3 (𝓞 ℚ) ℚ) : Continuous (MulAut.conj h) :=
  ((continuous_const.mul continuous_id).mul continuous_const).congr fun y => (MulAut.conj_apply h y).symm

p2m_export "LanglandsTunnell.CubicInduction" "continuous_conj"

private theorem isHaarMeasure_map_conj (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).IsHaarMeasure :=
  (MulAut.conj h).isHaarMeasure_map (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) (continuous_conj h)
    (((continuous_const.mul continuous_id).mul continuous_const).congr fun y => (MulAut.conj_symm_apply h y).symm)

attribute [local instance] isHaarMeasure_map_conj

private theorem integral_eq_haarScalarFactor_smul_integral_conj (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    ∫ k, f k ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) =
      ((((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
          (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : NNReal) : ℝ) •
        ∫ k, f (h⁻¹ * k * h) ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
  have hg : Continuous fun k => f (h⁻¹ * k * h) := hf.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hgs : HasCompactSupport fun k => f (h⁻¹ * k * h) :=
    hfs.comp_homeomorph ((Homeomorph.mulLeft h⁻¹).trans (Homeomorph.mulRight h))

  have hreal : ∀ u : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ, Continuous u → HasCompactSupport u →
      ∫ k, u k ∂((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)) =
        ((((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
            (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : NNReal) : ℝ) •
          ∫ k, u k ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    intro u hu hus
    rw [Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport _
      (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) hu hus, integral_smul_nnreal_measure, NNReal.smul_def]

  have hgi : Integrable (fun k => f (h⁻¹ * k * h)) (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) :=
    hg.integrable_of_hasCompactSupport hgs
  have hgi' : Integrable (fun k => f (h⁻¹ * k * h)) ((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)) :=
    hg.integrable_of_hasCompactSupport hgs
  have key : ∫ k, f (h⁻¹ * k * h) ∂((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)) =
      ((((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
          (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : NNReal) : ℝ) •
        ∫ k, f (h⁻¹ * k * h) ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by
    apply Complex.ext
    · rw [Complex.smul_re, smul_eq_mul, ← RCLike.re_to_complex, ← RCLike.re_to_complex, ← integral_re hgi',
        ← integral_re hgi]
      exact hreal _ (RCLike.continuous_re.comp hg) (hgs.comp_left (map_zero _))
    · rw [Complex.smul_im, smul_eq_mul, ← RCLike.im_to_complex, ← RCLike.im_to_complex, ← integral_im hgi',
        ← integral_im hgi]
      exact hreal _ (RCLike.continuous_im.comp hg) (hgs.comp_left (map_zero _))

  have hfun : (fun k => f k) = fun k => f (h⁻¹ * MulAut.conj h k * h) := by
    funext k
    rw [MulAut.conj_apply]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  calc ∫ k, f k ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
      = ∫ k, f (h⁻¹ * MulAut.conj h k * h) ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := by rw [hfun]
    _ = ∫ k, f (h⁻¹ * k * h) ∂((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)) :=
        (integral_map (continuous_conj h).measurable.aemeasurable hg.aestronglyMeasurable).symm
    _ = _ := key

private theorem haarScalarFactor_map_conj_pos (h : AdelicGL 3 (𝓞 ℚ) ℚ) :
    0 < ((((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
      (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : NNReal) : ℝ) :=
  NNReal.coe_pos.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _)

private theorem translateRight_smoothingOperator_apply (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {φ F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) (hF : Continuous F)
    (x : AdelicGL 3 (𝓞 ℚ) ℚ) :
    translateRight h (smoothingOperator φ F) x =
      ((((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
          (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : NNReal) : ℝ) •
        smoothingOperator (fun k => φ (h⁻¹ * k * h)) (translateRight h F) x := by
  rw [translateRight_apply, smoothingOperator_apply, smoothingOperator_apply]
  have hc : Continuous fun k => φ k * F (x * h * k) := hφ.mul (hF.comp (continuous_const.mul continuous_id))
  have hcs : HasCompactSupport fun k => φ k * F (x * h * k) := hφs.mul_right (f' := fun k => F (x * h * k))
  rw [integral_eq_haarScalarFactor_smul_integral_conj h hc hcs]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [translateRight_apply, mul_assoc, mul_inv_cancel_left]

private theorem isRapidlyDecreasingOnSiegel3_smoothingOperator (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hΦ₀ : IsSlabDomain a b Φ₀) (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀)
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hφ : IsSmoothingKernel φ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    IsRapidlyDecreasingOnSiegel3 (smoothingOperator φ F) := by
  intro h hh N c hc C

  have hφh : IsSmoothingKernel fun k => φ (h⁻¹ * k * h) := isSmoothingKernel_conj hφ hh
  obtain ⟨T, -, hT⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ₀
    exists_mul_eq_unipotent_mul_diagonal_mul_compact (fun k => φ (h⁻¹ * k * h)) hφh
  obtain ⟨CN, hCN⟩ := exists_mem_cuspFunctions_toL2_eq_and_norm_le_of_mem_cuspidalSubspace ω hω a b Φ₀ hΦ₀
    (fun k => φ (h⁻¹ * k * h)) hφh T hT

  obtain ⟨hmem, -, -⟩ :=
    exists_translateRight_mem_cuspFunctions_norm_toL2_eq_and_continuous ω hω a b Φ₀ hΦ₀ F hF
  obtain ⟨hRF, hTR⟩ := hT (translateRight h F) (hmem h)
  obtain ⟨F', hF', hTu, hdec⟩ := hCN ⟨toL2 ω a b Φ₀ ⟨translateRight h F, (hmem h).1⟩,
    toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ (hmem h)⟩

  have heq : F' = smoothingOperator (fun k => φ (h⁻¹ * k * h)) (translateRight h F) :=
    eq_of_toL2_eq ω a b Φ₀ hΦ₀ hF'.1 hF'.2.1 hRF.1 hRF.2.1 (hTu.symm.trans hTR)

  refine ⟨(((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
      (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : ℝ) * CN N c C *
      ‖(⟨toL2 ω a b Φ₀ ⟨translateRight h F, (hmem h).1⟩,
        toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ (hmem h)⟩ : ↥(cuspidalSubspace ω a b Φ₀))‖,
    fun n t k hx w => ?_⟩
  have hpos := haarScalarFactor_map_conj_pos h
  have h1 : smoothingOperator φ F (n * t * k * h) =
      (((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
        (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : ℝ) • F' (n * t * k) := by
    have h2 := translateRight_smoothingOperator_apply h hφc hφs hF.2.1 (n * t * k)
    rw [translateRight_apply] at h2
    rw [h2, heq]
  rw [h1, norm_smul, Real.norm_of_nonneg hpos.le]
  calc _ ≤ (((AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).map (MulAut.conj h)).haarScalarFactor
        (AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) : ℝ) * (CN N c C * ((archRoot₁ ℚ w t * archRoot₂ ℚ w t) ^ N)⁻¹ *
          ‖(⟨toL2 ω a b Φ₀ ⟨translateRight h F, (hmem h).1⟩,
            toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ (hmem h)⟩ : ↥(cuspidalSubspace ω a b Φ₀))‖) :=
        mul_le_mul_of_nonneg_left (hdec N c hc C n t k hx w) hpos.le
    _ = _ := by ring

section KernelFamily

private def entryMonomial {j : ℕ} (i : Fin j → Fin 3 × Fin 3) (m : Fin 3 → Fin 3 → ℝ) : ℝ :=
  ∏ t, m (i t).1 (i t).2

private def entryMonomials (d : ℕ) : Set ((Fin 3 → Fin 3 → ℝ) → ℝ) :=
  {f | ∃ j : ℕ, j ≤ d ∧ ∃ i : Fin j → Fin 3 × Fin 3, f = entryMonomial i}

private def entryPolySpace (d : ℕ) : Submodule ℝ ((Fin 3 → Fin 3 → ℝ) → ℝ) :=
  Submodule.span ℝ (entryMonomials d)

private def entryLeftMul (k m : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => ∑ c, k a c * m c b

private theorem entryMonomial_entryLeftMul {j : ℕ} (i : Fin j → Fin 3 × Fin 3) (k m : Fin 3 → Fin 3 → ℝ) :
    entryMonomial i (entryLeftMul k m) =
      ∑ c : Fin j → Fin 3, (∏ t, k (i t).1 (c t)) * entryMonomial (fun t => (c t, (i t).2)) m := by
  simp only [entryMonomial, entryLeftMul]
  rw [Finset.prod_univ_sum (fun _ => (Finset.univ : Finset (Fin 3))) (fun t c => k (i t).1 c * m c (i t).2),
    Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.prod_mul_distrib]

private theorem entryPolySpace_le_comap_funLeft (d : ℕ) (k : Fin 3 → Fin 3 → ℝ) :
    entryPolySpace d ≤ (entryPolySpace d).comap (LinearMap.funLeft ℝ ℝ (entryLeftMul k)) := by
  refine Submodule.span_le.mpr ?_
  rintro g ⟨j, hj, i, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  have key : LinearMap.funLeft ℝ ℝ (entryLeftMul k) (entryMonomial i) =
      ∑ c : Fin j → Fin 3, (∏ t, k (i t).1 (c t)) • (entryMonomial (fun t => (c t, (i t).2))) := by
    funext m
    simp only [LinearMap.funLeft_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact entryMonomial_entryLeftMul i k m
  rw [key]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, _, rfl⟩)

private theorem comp_entryLeftMul_mem_entryPolySpace {d : ℕ} {f : (Fin 3 → Fin 3 → ℝ) → ℝ}
    (hf : f ∈ entryPolySpace d) (k : Fin 3 → Fin 3 → ℝ) :
    (fun m => f (entryLeftMul k m)) ∈ entryPolySpace d :=
  entryPolySpace_le_comap_funLeft d k hf

private theorem finite_entryMonomials (d : ℕ) : (entryMonomials d).Finite := by
  have hsub : entryMonomials d ⊆
      Set.range (fun q : (Σ j : Fin (d + 1), (Fin j → Fin 3 × Fin 3)) => entryMonomial q.2) := by
    rintro f ⟨j, hj, i, rfl⟩
    exact ⟨⟨⟨j, Nat.lt_succ_of_le hj⟩, i⟩, rfl⟩
  exact (Set.finite_range _).subset hsub

private theorem entryMonomial_mul {j j' : ℕ} (i : Fin j → Fin 3 × Fin 3) (i' : Fin j' → Fin 3 × Fin 3)
    (m : Fin 3 → Fin 3 → ℝ) :
    entryMonomial i m * entryMonomial i' m = entryMonomial (Fin.append i i') m := by
  simp only [entryMonomial]
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

private theorem entryMonomial_single (a b : Fin 3) (m : Fin 3 → Fin 3 → ℝ) :
    entryMonomial (fun _ : Fin 1 => (a, b)) m = m a b := by
  simp [entryMonomial]

private theorem entryMonomial_zero (i : Fin 0 → Fin 3 × Fin 3) (m : Fin 3 → Fin 3 → ℝ) : entryMonomial i m = 1 := by
  simp [entryMonomial]

private theorem contDiff_det3 : ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det := by
  simp only [Matrix.det_fin_three, Matrix.of_apply]
  fun_prop

private theorem contDiff_entryMonomial {j : ℕ} (i : Fin j → Fin 3 × Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (entryMonomial i) := by
  unfold entryMonomial
  exact contDiff_prod fun t _ => contDiff_apply_apply ℝ ℝ (i t).1 (i t).2

private theorem contDiff_of_mem_entryPolySpace {d : ℕ} {P : (Fin 3 → Fin 3 → ℝ) → ℝ}
    (hP : P ∈ entryPolySpace d) : ContDiff ℝ (⊤ : ℕ∞) P := by
  unfold entryPolySpace at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, -, i, rfl⟩ := hx
    exact contDiff_entryMonomial i
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact contDiff_const.smul hx

private def idArray : Fin 3 → Fin 3 → ℝ := fun i j => if i = j then 1 else 0

private theorem of_idArray : Matrix.of idArray = 1 := by
  ext i j
  simp [idArray, Matrix.one_apply]

private def gram (m : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := fun i j => ∑ l, m l i * m l j

private theorem contDiff_gram : ContDiff ℝ (⊤ : ℕ∞) gram := by
  unfold gram
  fun_prop

open Matrix in
private theorem of_gram (m : Fin 3 → Fin 3 → ℝ) : Matrix.of (gram m) = (Matrix.of m)ᵀ * Matrix.of m := by
  ext i j
  simp [gram, Matrix.mul_apply]

private theorem gram_idArray : gram idArray = idArray := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [gram, idArray]

private theorem abs_le_sqrt_of_dist_gram_le {m : Fin 3 → Fin 3 → ℝ} {r : ℝ} (h : dist (gram m) idArray ≤ r)
    (l j : Fin 3) : |m l j| ≤ Real.sqrt (1 + r) := by
  apply Real.abs_le_sqrt
  have h1 : dist (gram m j j) (idArray j j) ≤ r := ((dist_le_pi_dist _ _ j).trans (dist_le_pi_dist _ _ j)).trans h
  have h2 : idArray j j = 1 := by simp [idArray]
  rw [h2, Real.dist_eq, abs_le] at h1
  have h3 : m l j ^ 2 ≤ gram m j j := by
    rw [sq]
    exact Finset.single_le_sum (f := fun l => m l j * m l j) (fun l _ => mul_self_nonneg (m l j)) (Finset.mem_univ l)
  linarith [h1.2]

private theorem exists_radius_det_ne_zero :
    ∃ r : ℝ, 0 < r ∧ ∀ m : Fin 3 → Fin 3 → ℝ, dist m idArray ≤ r → (Matrix.of m).det ≠ 0 := by
  have hc : ContinuousAt (fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det) idArray :=
    contDiff_det3.continuous.continuousAt
  obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.1 hc (1 / 2) one_half_pos
  refine ⟨δ / 2, half_pos hδ, fun m hm h0 => ?_⟩
  have h1 := h (lt_of_le_of_lt hm (half_lt_self hδ))
  rw [h0, of_idArray, Matrix.det_one, Real.dist_eq] at h1
  norm_num at h1

private def archFactor (β P : (Fin 3 → Fin 3 → ℝ) → ℝ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ((P m * β (gram m) : ℝ) : ℂ)

private theorem tsupport_archFactor_subset {β P : (Fin 3 → Fin 3 → ℝ) → ℝ} {r : ℝ}
    (hβs : Function.support β ⊆ Metric.ball idArray r) :
    tsupport (archFactor β P) ⊆ gram ⁻¹' Metric.closedBall idArray r := by
  refine closure_minimal (fun m hm => ?_) (Metric.isClosed_closedBall.preimage contDiff_gram.continuous)
  have hβm : β (gram m) ≠ 0 := fun h0 => hm (by simp [archFactor, h0])
  exact Metric.ball_subset_closedBall (hβs hβm)

private theorem isSmoothArchFactor_archFactor {β P : (Fin 3 → Fin 3 → ℝ) → ℝ} {r : ℝ}
    (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβs : Function.support β ⊆ Metric.ball idArray r)
    (hr : ∀ m : Fin 3 → Fin 3 → ℝ, dist m idArray ≤ r → (Matrix.of m).det ≠ 0) (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    IsSmoothArchFactor (archFactor β P) := by
  have hsub := tsupport_archFactor_subset (P := P) hβs
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) fun m => P m * β (gram m) := hP.mul (hβ.comp contDiff_gram)
    have h2 : archFactor β P = Complex.ofRealCLM ∘ fun m => P m * β (gram m) := by
      funext m
      simp [archFactor]
    rw [h2]
    exact Complex.ofRealCLM.contDiff.comp h1
  · refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 3 → Fin 3 → ℝ) (Real.sqrt (1 + r)))
      (isClosed_tsupport _) fun m hm => ?_
    have hgm : dist (gram m) idArray ≤ r := Metric.mem_closedBall.1 (hsub hm)
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro l
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro j
    rw [Real.norm_eq_abs]
    exact abs_le_sqrt_of_dist_gram_le hgm l j
  · intro m hm h0
    have hgm : dist (gram m) idArray ≤ r := Metric.mem_closedBall.1 (hsub hm)
    apply hr (gram m) hgm
    rw [of_gram, Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]

private theorem exists_bump {r : ℝ} (hr : 0 < r) :
    ∃ β : (Fin 3 → Fin 3 → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ (∀ m, 0 ≤ β m) ∧ β idArray = 1 ∧ Continuous β ∧
      Function.support β ⊆ Metric.ball idArray r := by
  let f : ContDiffBump idArray := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  exact ⟨f, f.contDiff, fun _ => f.nonneg, f.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hr).le),
    f.continuous, f.support_eq.subset⟩

private noncomputable def kernelOf (β P : (Fin 3 → Fin 3 → ℝ) → ℝ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))) :
    AdelicGL 3 (𝓞 ℚ) ℚ → ℂ :=
  fun k => archFactor β P (archEntries k) *
    Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) k

private theorem isSmoothingKernel_kernelOf {β P : (Fin 3 → Fin 3 → ℝ) → ℝ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hα : IsSmoothArchFactor (archFactor β P))
    (hK' : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
      IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hcof : ∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) :
    IsSmoothingKernel (kernelOf β P K') :=
  ⟨archFactor β P, K', hα, hK', hcof, fun _ => rfl⟩

private theorem componentAt3_mem_of_kernelOf_ne_zero {β P : (Fin 3 → Fin 3 → ℝ) → ℝ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    {g : AdelicGL 3 (𝓞 ℚ) ℚ} (hg : kernelOf β P K' g ≠ 0) (p : HeightOneSpectrum (𝓞 ℚ)) :
    componentAt3 (𝓞 ℚ) ℚ p g ∈ K' p := by
  by_contra hp
  apply hg
  have hg' : g ∉ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := fun h => hp (h p)
  unfold kernelOf
  rw [Set.indicator_of_notMem hg', mul_zero]

private theorem kernelOf_add (β P Q : (Fin 3 → Fin 3 → ℝ) → ℝ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))) :
    kernelOf β (P + Q) K' = kernelOf β P K' + kernelOf β Q K' := by
  funext k
  simp only [kernelOf, archFactor, Pi.add_apply]
  push_cast
  ring

private theorem kernelOf_smul (β : (Fin 3 → Fin 3 → ℝ) → ℝ) (c : ℝ) (P : (Fin 3 → Fin 3 → ℝ) → ℝ)
    (K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))) :
    kernelOf β (c • P) K' = (c : ℂ) • kernelOf β P K' := by
  funext k
  simp only [kernelOf, archFactor, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

private theorem exists_localSubgroups (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (V : (p : HeightOneSpectrum (𝓞 ℚ)) → Set (GL (Fin 3) (p.adicCompletion ℚ))) (hV : ∀ p, V p ∈ nhds 1)
    (hopen : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      IsOpen (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hcpt : ∀ p : HeightOneSpectrum (𝓞 ℚ),
      IsCompact (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (GL (Fin 3) (p.adicCompletion ℚ))))
    (hsmall : ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (W : Set (GL (Fin 3) (p.adicCompletion ℚ))), W ∈ nhds 1 →
      ∃ K : Subgroup (GL (Fin 3) (p.adicCompletion ℚ)), K ≤ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
        IsOpen (K : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧ IsCompact (K : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
        (K : Set (GL (Fin 3) (p.adicCompletion ℚ))) ⊆ W) :
    ∃ K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ)),
      (∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ∧
        IsCompact (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) ∧
      (∀ᶠ p in Filter.cofinite, K' p = localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      (∀ p, K' p ≤ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      ∀ p ∈ T, (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ))) ⊆ V p := by
  classical
  choose K hKle hKo hKc hKV using fun p => hsmall p (V p) (hV p)
  refine ⟨fun p => if p ∈ T then K p else localMaximalCompact3 (𝓞 ℚ) ℚ p, fun p => ?_, ?_, fun p => ?_,
    fun p hp => ?_⟩
  · by_cases hp : p ∈ T
    · simp only [hp, if_true]; exact ⟨hKo p, hKc p⟩
    · simp only [hp, if_false]; exact ⟨hopen p, hcpt p⟩
  · rw [Filter.eventually_cofinite]
    refine T.finite_toSet.subset fun p hp => ?_
    by_contra hpT
    exact hp (if_neg (by simpa using hpT))
  · by_cases hp : p ∈ T
    · simp only [hp, if_true]; exact hKle p
    · simp only [hp, if_false]; exact le_rfl
  · simp only [hp, if_true]; exact hKV p

end KernelFamily

section PolynomialDensity

private theorem entryPolySpace_mono {d d' : ℕ} (h : d ≤ d') : entryPolySpace d ≤ entryPolySpace d' :=
  Submodule.span_mono fun _ ⟨j, hj, i, hf⟩ => ⟨j, hj.trans h, i, hf⟩

private theorem mul_mem_entryPolySpace {d d' : ℕ} {P Q : (Fin 3 → Fin 3 → ℝ) → ℝ} (hP : P ∈ entryPolySpace d)
    (hQ : Q ∈ entryPolySpace d') : P * Q ∈ entryPolySpace (d + d') := by
  unfold entryPolySpace at hP hQ ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, hj, i, rfl⟩ := hx
    induction hQ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j', hj', i', rfl⟩ := hy
      refine Submodule.subset_span ⟨j + j', Nat.add_le_add hj hj', Fin.append i i', ?_⟩
      funext m
      exact entryMonomial_mul i i' m
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

private theorem const_mem_entryPolySpace (r : ℝ) (d : ℕ) :
    (fun _ => r : (Fin 3 → Fin 3 → ℝ) → ℝ) ∈ entryPolySpace d := by
  have h1 : (fun _ => (1 : ℝ) : (Fin 3 → Fin 3 → ℝ) → ℝ) ∈ entryPolySpace d :=
    Submodule.subset_span ⟨0, Nat.zero_le d, Fin.elim0, by funext m; exact (entryMonomial_zero _ m).symm⟩
  have h2 : (fun _ => r : (Fin 3 → Fin 3 → ℝ) → ℝ) = r • fun _ => (1 : ℝ) := by
    funext m
    simp
  rw [h2]
  exact Submodule.smul_mem _ r h1

private theorem coord_mem_entryPolySpace (a b : Fin 3) {d : ℕ} (hd : 1 ≤ d) :
    (fun m : Fin 3 → Fin 3 → ℝ => m a b) ∈ entryPolySpace d :=
  Submodule.subset_span ⟨1, hd, fun _ => (a, b), by funext m; exact (entryMonomial_single a b m).symm⟩

private def coordCM (a b : Fin 3) : C(Fin 3 → Fin 3 → ℝ, ℝ) :=
  ⟨fun m => m a b, (continuous_apply b).comp (continuous_apply a)⟩

private def coordSubalgebra : Subalgebra ℝ C(Fin 3 → Fin 3 → ℝ, ℝ) :=
  Algebra.adjoin ℝ (Set.range fun ab : Fin 3 × Fin 3 => coordCM ab.1 ab.2)

private theorem coordSubalgebra_separatesPoints : coordSubalgebra.SeparatesPoints := by
  intro x y hxy
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hxy
  obtain ⟨b, hb⟩ := Function.ne_iff.1 ha
  exact ⟨coordCM a b, ⟨coordCM a b, Algebra.subset_adjoin ⟨(a, b), rfl⟩, rfl⟩, hb⟩

private theorem exists_mem_entryPolySpace_of_mem_coordSubalgebra {g : C(Fin 3 → Fin 3 → ℝ, ℝ)}
    (hg : g ∈ coordSubalgebra) : ∃ d : ℕ, (g : (Fin 3 → Fin 3 → ℝ) → ℝ) ∈ entryPolySpace d := by
  unfold coordSubalgebra at hg
  induction hg using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact ⟨1, coord_mem_entryPolySpace a b le_rfl⟩
  | algebraMap r =>
    refine ⟨0, ?_⟩
    have h : ⇑(algebraMap ℝ C(Fin 3 → Fin 3 → ℝ, ℝ) r) = fun _ => r := by
      funext m
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h]
    exact const_mem_entryPolySpace r 0
  | add x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    refine ⟨max d d', ?_⟩
    rw [ContinuousMap.coe_add]
    exact Submodule.add_mem _ (entryPolySpace_mono (le_max_left _ _) hd) (entryPolySpace_mono (le_max_right _ _) hd')
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd⟩ := hx
    obtain ⟨d', hd'⟩ := hy
    refine ⟨d + d', ?_⟩
    rw [ContinuousMap.coe_mul]
    exact mul_mem_entryPolySpace hd hd'

private theorem exists_entryPoly_near (ψ : C(Fin 3 → Fin 3 → ℝ, ℝ)) {K : Set (Fin 3 → Fin 3 → ℝ)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (d : ℕ) (P : (Fin 3 → Fin 3 → ℝ) → ℝ), P ∈ entryPolySpace d ∧ ∀ x ∈ K, |P x - ψ x| < ε := by
  obtain ⟨g, hg, h⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    coordSubalgebra_separatesPoints ψ hK hε
  obtain ⟨d, hd⟩ := exists_mem_entryPolySpace_of_mem_coordSubalgebra hg
  exact ⟨d, g, hd, fun x hx => by simpa [Real.norm_eq_abs] using h x hx⟩

end PolynomialDensity

section NonVanishing

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private theorem exists_smoothingOperator_apply_ne_zero (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀)
    (hF0 : toL2 ω a b Φ₀ ⟨F, hF.1⟩ ≠ 0) {t : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ} (htc : Continuous t)
    (hts : HasCompactSupport t) (ht0 : ∀ k, 0 ≤ t k) (ht1 : t 1 ≠ 0)
    (hθF : smoothingOperator (fun k => (t k : ℂ)) F ∈ automorphicSubmodule ω a b Φ₀)
    (hFm : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, translateRight k F ∈ automorphicSubmodule ω a b Φ₀)
    (hcont : Continuous fun k : AdelicGL 3 (𝓞 ℚ) ℚ => toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩)
    (hpair : ∀ Y : Carrier a b Φ₀,
      ⟪Y, toL2 ω a b Φ₀ ⟨smoothingOperator (fun k => (t k : ℂ)) F, hθF⟩⟫_ℂ =
        ∫ k, (t k : ℂ) * ⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ
          ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    (hnear : ∀ k, t k ≠ 0 →
      ‖toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩ - toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ ≤ ‖toL2 ω a b Φ₀ ⟨F, hF.1⟩‖ / 2) :
    ∃ g : AdelicGL 3 (𝓞 ℚ) ℚ, smoothingOperator (fun k => (t k : ℂ)) F g ≠ 0 := by
  set η := AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hη
  set e₀ := toL2 ω a b Φ₀ ⟨F, hF.1⟩ with he₀
  set eθ := toL2 ω a b Φ₀ ⟨smoothingOperator (fun k => (t k : ℂ)) F, hθF⟩ with heθ
  set Z : ℝ := ∫ k, t k ∂η with hZ
  have hZpos : 0 < Z := htc.integral_pos_of_hasCompactSupport_nonneg_nonzero hts (fun k => ht0 k) ht1
  have hti : Integrable t η := htc.integrable_of_hasCompactSupport hts

  set V := eθ - (Z : ℂ) • e₀ with hV
  have hbound : ∀ Y : Carrier a b Φ₀, ‖⟪Y, V⟫_ℂ‖ ≤ ‖Y‖ * (‖e₀‖ / 2) * Z := by
    intro Y
    have hci : Continuous fun k => ⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ := continuous_const.inner hcont
    have hθs : HasCompactSupport fun k => (t k : ℂ) := hts.comp_left Complex.ofReal_zero
    have hi1 : Integrable (fun k => (t k : ℂ) * ⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ) η :=
      ((Complex.continuous_ofReal.comp htc).mul hci).integrable_of_hasCompactSupport hθs.mul_right
    have hi2 : Integrable (fun k => (t k : ℂ) * ⟪Y, e₀⟫_ℂ) η :=
      ((Complex.continuous_ofReal.comp htc).integrable_of_hasCompactSupport hθs).mul_const _
    have h1 : ⟪Y, V⟫_ℂ = ∫ k, (t k : ℂ) * (⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ - ⟪Y, e₀⟫_ℂ) ∂η := by
      have h2 : (∫ k, (t k : ℂ) * (⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ - ⟪Y, e₀⟫_ℂ) ∂η) =
          (∫ k, (t k : ℂ) * ⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ ∂η) -
            ∫ k, (t k : ℂ) * ⟪Y, e₀⟫_ℂ ∂η := by
        rw [← integral_sub hi1 hi2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [mul_sub]
      rw [h2, integral_mul_const, integral_complex_ofReal, ← hZ, hV, heθ, inner_sub_right, inner_smul_right, hpair Y]
    rw [h1]
    calc ‖∫ k, (t k : ℂ) * (⟪Y, toL2 ω a b Φ₀ ⟨translateRight k F, hFm k⟩⟫_ℂ - ⟪Y, e₀⟫_ℂ) ∂η‖
        ≤ ∫ k, t k * (‖Y‖ * (‖e₀‖ / 2)) ∂η := by
          refine norm_integral_le_of_norm_le (hti.mul_const _) (Filter.Eventually.of_forall fun k => ?_)
          rw [norm_mul, Complex.norm_of_nonneg (ht0 k), ← inner_sub_right]
          by_cases hk : t k = 0
          · simp [hk]
          · exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_left (hnear k hk) (norm_nonneg _))) (ht0 k)
      _ = (∫ k, t k ∂η) * (‖Y‖ * (‖e₀‖ / 2)) := integral_mul_const _ _
      _ = ‖Y‖ * (‖e₀‖ / 2) * Z := by rw [← hZ]; ring

  have hVn : ‖V‖ ≤ ‖e₀‖ / 2 * Z := by
    have h := hbound V
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at h
    by_cases hV0 : ‖V‖ = 0
    · rw [hV0]
      exact mul_nonneg (by positivity) hZpos.le
    · have hVp : 0 < ‖V‖ := (norm_nonneg _).lt_of_ne (Ne.symm hV0)
      rw [sq, mul_assoc] at h
      exact le_of_mul_le_mul_left h hVp

  have hne : eθ ≠ 0 := by
    intro h0
    have h1 : ‖(Z : ℂ) • e₀‖ ≤ ‖e₀‖ / 2 * Z := by
      have h2 : V = -((Z : ℂ) • e₀) := by rw [hV, h0, zero_sub]
      rw [← norm_neg, ← h2]
      exact hVn
    rw [norm_smul, Complex.norm_of_nonneg hZpos.le] at h1
    have h2 : 0 < ‖e₀‖ := norm_pos_iff.2 hF0
    nlinarith [mul_pos hZpos h2]

  by_contra hall
  simp only [not_exists, ne_eq, not_not] at hall
  apply hne
  have hz : (⟨smoothingOperator (fun k => (t k : ℂ)) F, hθF⟩ : ↥(automorphicSubmodule ω a b Φ₀)) = 0 := by
    apply Subtype.ext
    funext g
    simp [hall g]
  rw [heθ, hz, map_zero]

private theorem exists_poly_integral_ne_zero {r : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ} (hrc : Continuous r)
    (hrs : HasCompactSupport r) (hr0 : ∀ k, 0 ≤ r k) {G : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hG : Continuous G)
    (haE : Continuous (archEntries : AdelicGL 3 (𝓞 ℚ) ℚ → Fin 3 → Fin 3 → ℝ))
    (ψ : C(Fin 3 → Fin 3 → ℝ, ℝ))
    {poly : ℕ → Set ((Fin 3 → Fin 3 → ℝ) → ℝ)}
    (hdense : ∀ (K : Set (Fin 3 → Fin 3 → ℝ)), IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ (d : ℕ) (P : (Fin 3 → Fin 3 → ℝ) → ℝ), P ∈ poly d ∧ ∀ x ∈ K, |P x - ψ x| < ε)
    (hpolyc : ∀ (d : ℕ) (P : (Fin 3 → Fin 3 → ℝ) → ℝ), P ∈ poly d → Continuous P)
    (hne : (∫ k, (ψ (archEntries k) : ℂ) * ((r k : ℂ) * G k) ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) ≠ 0) :
    ∃ (d : ℕ) (P : (Fin 3 → Fin 3 → ℝ) → ℝ), P ∈ poly d ∧
      (∫ k, (P (archEntries k) : ℂ) * ((r k : ℂ) * G k) ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) ≠ 0 := by
  set η := AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ with hη
  set Λ₀ := ∫ k, (ψ (archEntries k) : ℂ) * ((r k : ℂ) * G k) ∂η with hΛ₀

  have hK : IsCompact (archEntries '' tsupport r) := hrs.image haE
  set M : ℝ := ∫ k, r k * ‖G k‖ ∂η with hM
  have hM0 : 0 ≤ M := integral_nonneg fun k => mul_nonneg (hr0 k) (norm_nonneg _)
  have hrGi : Integrable (fun k => r k * ‖G k‖) η :=
    (hrc.mul hG.norm).integrable_of_hasCompactSupport hrs.mul_right

  have hδ : 0 < ‖Λ₀‖ / (M + 1) := div_pos (norm_pos_iff.2 hne) (by linarith)
  obtain ⟨d, P, hP, hPψ⟩ := hdense _ hK _ hδ
  refine ⟨d, P, hP, fun h0 => ?_⟩

  have hint : ∀ w : (Fin 3 → Fin 3 → ℝ) → ℝ, Continuous w →
      Integrable (fun k => (w (archEntries k) : ℂ) * ((r k : ℂ) * G k)) η := by
    intro w hw
    refine (((Complex.continuous_ofReal.comp (hw.comp haE)).mul
      ((Complex.continuous_ofReal.comp hrc).mul hG)).integrable_of_hasCompactSupport ?_)
    exact ((hrs.comp_left Complex.ofReal_zero).mul_right).mul_left

  have hdiff : ‖Λ₀ - ∫ k, (P (archEntries k) : ℂ) * ((r k : ℂ) * G k) ∂η‖ ≤ ‖Λ₀‖ / (M + 1) * M := by
    rw [hΛ₀, ← integral_sub (hint ψ ψ.continuous) (hint P (hpolyc d P hP))]
    calc _ ≤ ∫ k, ‖Λ₀‖ / (M + 1) * (r k * ‖G k‖) ∂η := by
          refine norm_integral_le_of_norm_le (hrGi.const_mul _) (Filter.Eventually.of_forall fun k => ?_)
          rw [← sub_mul, norm_mul, norm_mul, Complex.norm_of_nonneg (hr0 k), ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs]
          by_cases hk : r k = 0
          · simp [hk]
          · have hk' : archEntries k ∈ archEntries '' tsupport r := ⟨k, subset_tsupport _ hk, rfl⟩
            have h1 : |ψ (archEntries k) - P (archEntries k)| ≤ ‖Λ₀‖ / (M + 1) := by
              rw [abs_sub_comm]
              exact (hPψ _ hk').le
            exact mul_le_mul_of_nonneg_right h1 (mul_nonneg (hr0 k) (norm_nonneg _))
      _ = ‖Λ₀‖ / (M + 1) * M := by rw [integral_const_mul, ← hM]
  have hlt : ‖Λ₀‖ / (M + 1) * M < ‖Λ₀‖ := by
    have h1 : ‖Λ₀‖ / (M + 1) * M = ‖Λ₀‖ * (M / (M + 1)) := by ring
    rw [h1]
    have h2 : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    nlinarith [norm_pos_iff.2 hne]
  rw [h0, sub_zero] at hdiff
  exact absurd (hdiff.trans_lt hlt) (lt_irrefl _)

end NonVanishing

section ArchSmoothHelpers

private noncomputable def realToInfiniteAdele : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

private theorem realToInfiniteAdele_apply (r : ℝ) : realToInfiniteAdele r = StandardKernel.ofReal r := rfl

private theorem realCoordinate_realToInfiniteAdele (r : ℝ) : realCoordinate (realToInfiniteAdele r) = r :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply r

private noncomputable def archInclMonoidHom :
    Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) →* Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) where
  toFun := archMatrixInclN (Fin 3) ℚ
  map_one' := archMatrixInclN_one (Fin 3) ℚ
  map_mul' := archMatrixInclN_mul (Fin 3) ℚ

private theorem archRealMat3_eq (e : Fin 3 → Fin 3 → ℝ) :
    WhittakerBlock.archRealMat3 e = archInclMonoidHom (realToInfiniteAdele.mapMatrix (Matrix.of e)) := rfl

private theorem isUnit_archRealMat3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    IsUnit (WhittakerBlock.archRealMat3 e) := by
  rw [archRealMat3_eq]
  exact (((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr he)).map
    realToInfiniteAdele.mapMatrix).map archInclMonoidHom

private theorem coe_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  rw [WhittakerBlock.archRealLift3, dif_pos (isUnit_archRealMat3 he)]
  exact (isUnit_archRealMat3 he).unit_spec

private theorem archRealLift3_mul {e e' : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (he' : (Matrix.of e').det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of e') =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 e' := by
  have hmul : (Matrix.of (Matrix.of e * Matrix.of e' : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    change (Matrix.of e * Matrix.of e').det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero he he'
  apply Units.ext
  rw [Units.val_mul, coe_archRealLift3 hmul, coe_archRealLift3 he, coe_archRealLift3 he', archRealMat3_eq,
    archRealMat3_eq, archRealMat3_eq]
  change archInclMonoidHom (realToInfiniteAdele.mapMatrix (Matrix.of e * Matrix.of e')) = _
  rw [map_mul, map_mul]

private theorem archRealLift3_one : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  have h1 : (Matrix.of (1 : Matrix (Fin 3) (Fin 3) ℝ)).det ≠ 0 := by
    change (1 : Matrix (Fin 3) (Fin 3) ℝ).det ≠ 0
    rw [Matrix.det_one]
    exact one_ne_zero
  apply Units.ext
  rw [coe_archRealLift3 h1, archRealMat3_eq, Units.val_one]
  change archInclMonoidHom (realToInfiniteAdele.mapMatrix (1 : Matrix (Fin 3) (Fin 3) ℝ)) = 1
  rw [map_one, map_one]

private theorem archEntries_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    archEntries (WhittakerBlock.archRealLift3 e) = e := by
  funext i j
  have h := congrFun (congrFun (archEntries_eq (WhittakerBlock.archRealLift3 e)) i) j
  rw [Matrix.of_apply] at h
  rw [h, coe_archRealLift3 he, archRealMat3_eq]
  exact realCoordinate_realToInfiniteAdele (e i j)

private theorem componentAt3_archRealLift3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0)
    (p : HeightOneSpectrum (𝓞 ℚ)) : componentAt3 (𝓞 ℚ) ℚ p (WhittakerBlock.archRealLift3 e) = 1 := by
  apply Units.ext
  change (AdelicLevel.finAdeleEval (𝓞 ℚ) ℚ p).mapMatrix ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
    (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) = 1
  have hfin : (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
      (WhittakerBlock.archRealLift3 e : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [coe_archRealLift3 he, archRealMat3_eq]
    refine Matrix.ext fun i j => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact adeleFin_archMatrixInclN (Fin 3) ℚ _ i j
  rw [hfin, map_one]

private theorem continuous_archEntries' : Continuous archEntries := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hrow : Continuous fun a : AdelicGL 3 (𝓞 ℚ) ℚ => (a : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i :=
    Matrix.GeneralLinearGroup.continuous_apply (fun a => a) continuous_id i
  exact continuous_realCoordinate.comp (continuous_fst.comp ((continuous_apply j).comp hrow))

private theorem
    aestronglyMeasurable_of_iteratedFDeriv_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : E → X → V} {e : E}
    (h : AEStronglyMeasurable (fun x => iteratedFDeriv ℝ 0 (fun e => H e x) e) μ) :
    AEStronglyMeasurable (fun x => H e x) μ := by
  have : (fun x => H e x) =
      fun x => continuousMultilinearCurryFin0 ℝ E V (iteratedFDeriv ℝ 0 (fun e => H e x) e) := by
    funext x
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [this]
  exact (continuousMultilinearCurryFin0 ℝ E V).continuous.comp_aestronglyMeasurable h

private theorem
    hasFDerivAt_integral_of_dominated_all_orders
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {U : Set E} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (hU : IsOpen U)
    {G : E → X → V}
    (hsm : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (fun e => G e x) U)
    (hmeas : ∀ k : ℕ, ∀ e ∈ U, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (fun e => G e x) e) μ)
    (hdom : ∀ K ⊆ U, IsCompact K → ∀ k : ℕ, ∃ b : X → ℝ, Integrable b μ ∧
      ∀ e ∈ K, ∀ x, ‖iteratedFDeriv ℝ k (fun e => G e x) e‖ ≤ b x)
    {e₀ : E} (he₀ : e₀ ∈ U) :
    HasFDerivAt (fun e => ∫ x, G e x ∂μ) (∫ x, fderiv ℝ (fun e => G e x) e₀ ∂μ) e₀ := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU e₀ he₀
  have hsub : Metric.closedBall e₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  obtain ⟨b₀, hb₀, hle₀⟩ := hdom _ hsub (isCompact_closedBall e₀ (r / 2)) 0
  obtain ⟨b₁, hb₁, hle₁⟩ := hdom _ hsub (isCompact_closedBall e₀ (r / 2)) 1
  have hmem : Metric.closedBall e₀ (r / 2) ∈ nhds e₀ := Metric.closedBall_mem_nhds e₀ (half_pos hr)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun e x => fderiv ℝ (fun e => G e x) e) hmem ?_ ?_
    ?_ ?_ hb₁ ?_
  · exact Filter.eventually_of_mem (hU.mem_nhds he₀) fun e he =>
      aestronglyMeasurable_of_iteratedFDeriv_zero (hmeas 0 e he)
  · refine Integrable.mono' hb₀ (aestronglyMeasurable_of_iteratedFDeriv_zero (hmeas 0 e₀ he₀))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fun e => G e x) (x := e₀)]
    exact hle₀ e₀ (Metric.mem_closedBall_self (half_pos hr).le) x
  · refine aestronglyMeasurable_of_iteratedFDeriv_zero (H := fun e x => fderiv ℝ (fun e => G e x) e) ?_
    have hrepr : (fun x => iteratedFDeriv ℝ 0 (fun e => fderiv ℝ (fun e => G e x) e) e₀) = fun x =>
        continuousMultilinearCurryRightEquiv' ℝ 0 E V (iteratedFDeriv ℝ (0 + 1) (fun e => G e x) e₀) := by
      funext x
      rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
    rw [hrepr]
    exact (continuousMultilinearCurryRightEquiv' ℝ 0 E V).continuous.comp_aestronglyMeasurable
      (hmeas 1 e₀ he₀)
  · refine Filter.Eventually.of_forall fun x e he => ?_
    calc ‖fderiv ℝ (fun e => G e x) e‖ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ fun e => G e x) e‖ :=
          (norm_iteratedFDeriv_zero).symm
      _ = ‖iteratedFDeriv ℝ (0 + 1) (fun e => G e x) e‖ := norm_iteratedFDeriv_fderiv
      _ ≤ b₁ x := hle₁ e he x
  · refine Filter.Eventually.of_forall fun x e he => ?_
    exact (((hsm x).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds (hsub he))).hasFDerivAt

private theorem
    contDiffOn_integral_of_dominated_aux
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {U : Set E} (hU : IsOpen U) (n : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {G : E → X → V},
      (∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (fun e => G e x) U) →
      (∀ k : ℕ, ∀ e ∈ U, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (fun e => G e x) e) μ) →
      (∀ K ⊆ U, IsCompact K → ∀ k : ℕ, ∃ b : X → ℝ, Integrable b μ ∧
        ∀ e ∈ K, ∀ x, ‖iteratedFDeriv ℝ k (fun e => G e x) e‖ ≤ b x) →
      ContDiffOn ℝ n (fun e => ∫ x, G e x ∂μ) U := by
  induction n with
  | zero =>
    intro V _ _ _ G hsm hmeas hdom
    rw [Nat.cast_zero, contDiffOn_zero]
    intro e₀ he₀
    exact (hasFDerivAt_integral_of_dominated_all_orders hU hsm hmeas hdom he₀).continuousAt.continuousWithinAt
  | succ n ih =>
    intro V _ _ _ G hsm hmeas hdom
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun e₀ he₀ => (hasFDerivAt_integral_of_dominated_all_orders hU hsm hmeas hdom he₀).differentiableAt
      |>.differentiableWithinAt, fun h => absurd h (WithTop.natCast_ne_top n), ?_⟩
    have hderiv : ∀ e₀ ∈ U, fderiv ℝ (fun e => ∫ x, G e x ∂μ) e₀ = ∫ x, fderiv ℝ (fun e => G e x) e₀ ∂μ :=
      fun e₀ he₀ => (hasFDerivAt_integral_of_dominated_all_orders hU hsm hmeas hdom he₀).fderiv
    refine (ih (G := fun e x => fderiv ℝ (fun e => G e x) e) ?_ ?_ ?_).congr fun e₀ he₀ => hderiv e₀ he₀
    · intro x
      exact (hsm x).fderiv_of_isOpen hU (by exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))
    · intro k e he
      have hrepr : (fun x => iteratedFDeriv ℝ k (fun e => fderiv ℝ (fun e => G e x) e) e) = fun x =>
          continuousMultilinearCurryRightEquiv' ℝ k E V (iteratedFDeriv ℝ (k + 1) (fun e => G e x) e) := by
        funext x
        rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]
      rw [hrepr]
      exact (continuousMultilinearCurryRightEquiv' ℝ k E V).continuous.comp_aestronglyMeasurable
        (hmeas (k + 1) e he)
    · intro K hK hKc k
      obtain ⟨b, hb, hle⟩ := hdom K hK hKc (k + 1)
      refine ⟨b, hb, fun e he x => ?_⟩
      rw [norm_iteratedFDeriv_fderiv (f := fun e => G e x)]
      exact hle e he x

private theorem
    contDiffOn_integral_of_dominated
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : Type} [MeasurableSpace X] {μ : Measure X}
    {U : Set E} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (hU : IsOpen U)
    {G : E → X → V}
    (hsm : ∀ x, ContDiffOn ℝ (⊤ : ℕ∞) (fun e => G e x) U)
    (hmeas : ∀ k : ℕ, ∀ e ∈ U, AEStronglyMeasurable (fun x => iteratedFDeriv ℝ k (fun e => G e x) e) μ)
    (hdom : ∀ K ⊆ U, IsCompact K → ∀ k : ℕ, ∃ b : X → ℝ, Integrable b μ ∧
      ∀ e ∈ K, ∀ x, ‖iteratedFDeriv ℝ k (fun e => G e x) e‖ ≤ b x) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e => ∫ x, G e x ∂μ) U :=
  contDiffOn_infty.mpr fun n => contDiffOn_integral_of_dominated_aux hU n hsm hmeas hdom

private noncomputable def invEntries3 (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ := Matrix.of.symm (Matrix.of e)⁻¹

private theorem contDiff_adjugate3 (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).adjugate i j := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_three] <;> fun_prop

private theorem contDiffOn_invEntries3 :
    ContDiffOn ℝ (⊤ : ℕ∞) invEntries3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  refine ContDiffOn.congr (f := fun e i j => ((Matrix.of e).det)⁻¹ * (Matrix.of e).adjugate i j) ?_ ?_
  · refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
    exact (contDiff_det3.contDiffOn.inv fun e he => he).mul (contDiff_adjugate3 i j).contDiffOn
  · intro e he
    funext i j
    simp only [invEntries3, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.of_symm_apply, Matrix.smul_apply,
      smul_eq_mul]

private noncomputable def mulEntries3 (q : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ)) : Fin 3 → Fin 3 → ℝ :=
  Matrix.of.symm (Matrix.of q.1 * Matrix.of q.2)

private theorem contDiff_mulEntries3 : ContDiff ℝ (⊤ : ℕ∞) mulEntries3 := by
  have hrepr : mulEntries3 = fun q i j => ∑ l, q.1 i l * q.2 l j := by
    funext q i j
    simp only [mulEntries3, Matrix.of_symm_apply, Matrix.mul_apply, Matrix.of_apply]
  rw [hrepr]
  fun_prop

private theorem det_of_invEntries3 {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (Matrix.of (invEntries3 e)).det ≠ 0 := by
  rw [invEntries3, Equiv.apply_symm_apply, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero he

private theorem archRealLift3_inv {e : Fin 3 → Fin 3 → ℝ} (he : (Matrix.of e).det ≠ 0) :
    (WhittakerBlock.archRealLift3 e)⁻¹ = WhittakerBlock.archRealLift3 (invEntries3 e) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← archRealLift3_mul he (det_of_invEntries3 he)]
  have h1 : Matrix.of e * Matrix.of (invEntries3 e) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [invEntries3, Equiv.apply_symm_apply]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr he)
  rw [h1, archRealLift3_one]

private theorem continuous_archRealMat3 : Continuous WhittakerBlock.archRealMat3 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  change Continuous fun e : Fin 3 → Fin 3 → ℝ =>
    ((AutomorphicForm.StandardKernel.ofReal (e i j), (1 : Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) :
      InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ)
  exact (AutomorphicForm.StandardKernel.continuous_ofReal.comp
    ((continuous_apply j).comp (continuous_apply i))).prodMk continuous_const

private theorem continuousOn_archRealLift3 :
    ContinuousOn WhittakerBlock.archRealLift3 {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine (continuous_archRealMat3.comp continuous_subtype_val).congr fun e => ?_
    exact (coe_archRealLift3 e.2).symm
  · have hinv : ContinuousOn (fun e => WhittakerBlock.archRealMat3 (invEntries3 e))
        {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} :=
      continuous_archRealMat3.comp_continuousOn contDiffOn_invEntries3.continuousOn
    refine (continuousOn_iff_continuous_restrict.mp hinv).congr fun e => ?_
    show WhittakerBlock.archRealMat3 (invEntries3 e.1) =
      ((WhittakerBlock.archRealLift3 e.1)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ).val
    rw [archRealLift3_inv e.2, coe_archRealLift3 (det_of_invEntries3 e.2)]

private theorem iteratedFDeriv_partial_eq {E P V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E × P → V}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (n : ℕ) (e : E) (m : P) :
    iteratedFDeriv ℝ n (fun e' => Φ (e', m)) e =
      (iteratedFDeriv ℝ n Φ (e, m)).compContinuousLinearMap fun _ => ContinuousLinearMap.inl ℝ E P := by
  have h1 : (fun e' => Φ (e', m)) = (fun q => Φ (q + ((0 : E), m))) ∘ ContinuousLinearMap.inl ℝ E P := by
    funext e'
    simp only [Function.comp_apply, ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun q : E × P => Φ (q + ((0 : E), m)) := hΦ.comp (contDiff_id.add contDiff_const)
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ h2 _ (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)),
    iteratedFDeriv_comp_add_right]
  simp only [ContinuousLinearMap.inl_apply, Prod.mk_add_mk, add_zero, zero_add]

private theorem exists_bound_iteratedFDeriv_partial {E P V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E × P → V}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (n : ℕ) {K : Set E} (hK : IsCompact K) {C : Set P} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ e ∈ K, ∀ m ∈ C, ‖iteratedFDeriv ℝ n (fun e' => Φ (e', m)) e‖ ≤ B := by
  obtain ⟨B₀, hB₀⟩ := (hK.prod hC).exists_bound_of_continuousOn
    (hΦ.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))).continuousOn
  refine ⟨B₀ * ∏ _i : Fin n, ‖ContinuousLinearMap.inl ℝ E P‖, fun e he m hm => ?_⟩
  rw [iteratedFDeriv_partial_eq hΦ]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hB₀ (e, m) ⟨he, hm⟩) (Finset.prod_nonneg fun _ _ => norm_nonneg _)

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

private theorem kernel_archRealLift3_mul {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ x, φ x = α (archEntries x) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) x)
    {d : Fin 3 → Fin 3 → ℝ} (hd : (Matrix.of d).det ≠ 0) (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    φ (WhittakerBlock.archRealLift3 d * k) =
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) k *
        α (mulEntries3 (d, archEntries k)) := by
  have harch : archEntries (WhittakerBlock.archRealLift3 d * k) = mulEntries3 (d, archEntries k) := by
    have h := archEntries_mul (WhittakerBlock.archRealLift3 d) k
    rw [archEntries_archRealLift3 hd] at h
    exact Matrix.of.apply_eq_iff_eq_symm_apply.mp h
  have hmem : WhittakerBlock.archRealLift3 d * k ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} ↔
      k ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} := by
    simp only [Set.mem_setOf_eq, map_mul, componentAt3_archRealLift3 hd, one_mul]
  rw [hφ, harch]
  by_cases hk : k ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
  · rw [Set.indicator_of_mem (hmem.mpr hk), Set.indicator_of_mem hk, mul_comm]
  · rw [Set.indicator_of_notMem (fun h => hk (hmem.mp h)), Set.indicator_of_notMem hk, mul_zero, zero_mul]

open scoped Pointwise in

private theorem contDiffOn_integral_kernel_archRealLift3 {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hL : MeasurableSet {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p})
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ x, φ x = α (archEntries x) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) x)
    (hφc : HasCompactSupport φ) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun d : Fin 3 → Fin 3 → ℝ => ∫ k, φ (WhittakerBlock.archRealLift3 d * k) * F (g * k)
        ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
      {d : Fin 3 → Fin 3 → ℝ | (Matrix.of d).det ≠ 0} := by
  set L := {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} with hLdef
  set U : Set (Fin 3 → Fin 3 → ℝ) := {d | (Matrix.of d).det ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne.preimage contDiff_det3.continuous
  set c : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun k => L.indicator (fun _ => (1 : ℂ)) k * F (g * k) with hcdef
  set Φ : (Fin 3 → Fin 3 → ℝ) × (Fin 3 → Fin 3 → ℝ) → ℂ := fun q => α (mulEntries3 q) with hΦdef
  have hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ := hα.1.comp contDiff_mulEntries3
  have hΦk : ∀ m, ContDiff ℝ (⊤ : ℕ∞) fun d => Φ (d, m) := fun m => hΦs.comp (contDiff_id.prodMk contDiff_const)

  have hint : ∀ d ∈ U, ∀ k, φ (WhittakerBlock.archRealLift3 d * k) * F (g * k) = c k • Φ (d, archEntries k) := by
    intro d hd k
    rw [kernel_archRealLift3_mul hφ hd, smul_eq_mul]
    ring
  have hder : ∀ (n : ℕ) (d : Fin 3 → Fin 3 → ℝ) (k : AdelicGL 3 (𝓞 ℚ) ℚ),
      iteratedFDeriv ℝ n (fun d => c k • Φ (d, archEntries k)) d =
        c k • iteratedFDeriv ℝ n (fun d => Φ (d, archEntries k)) d := by
    intro n d k
    have h1 : ContDiffAt ℝ n (fun d => Φ (d, archEntries k)) d :=
      (hΦk (archEntries k)).contDiffAt.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
    exact iteratedFDeriv_const_smul_apply' h1
  have hc_meas : StronglyMeasurable c :=
    (stronglyMeasurable_const.indicator hL).mul (hF.comp (continuous_const_mul g)).stronglyMeasurable
  have hM_meas : StronglyMeasurable archEntries := continuous_archEntries'.stronglyMeasurable
  refine ContDiffOn.congr (f := fun d => ∫ k, c k • Φ (d, archEntries k) ∂(AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ))
    ?_ fun d hd => integral_congr_ae (Filter.Eventually.of_forall fun k => hint d hd k)
  refine contDiffOn_integral_of_dominated hUo (fun k => ((hΦk (archEntries k)).const_smul (c k)).contDiffOn) ?_ ?_
  ·
    intro n d _
    simp only [hder]
    refine (hc_meas.smul ?_).aestronglyMeasurable
    have hcont : Continuous fun m : Fin 3 → Fin 3 → ℝ => iteratedFDeriv ℝ n (fun d => Φ (d, m)) d := by
      simp only [iteratedFDeriv_partial_eq hΦs]
      exact (ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Fin 3 → Fin 3 → ℝ) (Fin 3 → Fin 3 → ℝ))).continuous.comp
        ((hΦs.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp (continuous_const.prodMk continuous_id))
    exact hcont.comp_stronglyMeasurable hM_meas
  ·
    intro K hKU hK n
    obtain ⟨K₁, hK₁, hKK₁, hK₁U⟩ := exists_compact_between hK hUo hKU

    set Cx : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
      ((fun d => WhittakerBlock.archRealLift3 (invEntries3 d)) '' K₁) * tsupport φ with hCxdef
    have hCx : IsCompact Cx := by
      refine IsCompact.mul (hK₁.image_of_continuousOn ?_) hφc
      exact continuousOn_archRealLift3.comp (contDiffOn_invEntries3.continuousOn.mono hK₁U) fun d hd =>
        det_of_invEntries3 (hK₁U hd)
    obtain ⟨B, hB⟩ := exists_bound_iteratedFDeriv_partial hΦs n hK₁ (hCx.image continuous_archEntries')
    obtain ⟨MF, hMF⟩ := hCx.exists_bound_of_continuousOn (hF.comp (continuous_const_mul g)).continuousOn
    refine ⟨Cx.indicator fun _ => MF * B, ?_, fun d hd k => ?_⟩
    · rw [integrable_indicator_iff hCx.measurableSet]
      exact integrableOn_const hCx.measure_lt_top.ne
    by_cases hk : k ∈ Cx
    · rw [Set.indicator_of_mem hk, hder, norm_smul]
      have hck : ‖c k‖ ≤ MF := by
        calc ‖c k‖ = ‖L.indicator (fun _ => (1 : ℂ)) k‖ * ‖F (g * k)‖ := norm_mul _ _
          _ ≤ 1 * ‖F (g * k)‖ := by
              gcongr
              exact (norm_indicator_le_norm_self _ _).trans (le_of_eq norm_one)
          _ = ‖F (g * k)‖ := one_mul _
          _ ≤ MF := hMF k hk
      exact mul_le_mul hck (hB d (interior_subset (hKK₁ hd)) _ (Set.mem_image_of_mem _ hk)) (norm_nonneg _)
        ((norm_nonneg _).trans hck)
    · rw [Set.indicator_of_notMem hk]

      have hzero : (fun d' => c k • Φ (d', archEntries k)) =ᶠ[nhds d] fun _ => (0 : ℂ) := by
        refine Filter.eventually_of_mem (mem_interior_iff_mem_nhds.mp (hKK₁ hd)) fun d' hd' => ?_
        have hd'U : d' ∈ U := hK₁U hd'
        have hnot : WhittakerBlock.archRealLift3 d' * k ∉ tsupport φ := by
          intro hmem
          apply hk
          have hk' : k = WhittakerBlock.archRealLift3 (invEntries3 d') * (WhittakerBlock.archRealLift3 d' * k) := by
            rw [← archRealLift3_inv hd'U, inv_mul_cancel_left]
          rw [hk']
          exact Set.mul_mem_mul (Set.mem_image_of_mem _ hd') hmem
        have h0 := image_eq_zero_of_notMem_tsupport hnot
        show c k • Φ (d', archEntries k) = 0
        rw [← hint d' hd'U k, h0, zero_mul]
      exact le_of_eq (by rw [(hzero.iteratedFDeriv ℝ n).eq_of_nhds, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero])

private theorem isArchSmooth3_smoothingOperator {α : (Fin 3 → Fin 3 → ℝ) → ℂ} (hα : IsSmoothArchFactor α)
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hL : MeasurableSet {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p})
    {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ x, φ x = α (archEntries x) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) x)
    (hφc : HasCompactSupport φ) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : Continuous F) :
    WhittakerBlock.IsArchSmooth3 (smoothingOperator φ F) := by
  intro g
  have hsmooth := (contDiffOn_integral_kernel_archRealLift3 hα hL hφ hφc hF g).comp contDiffOn_invEntries3
    fun e (he : (Matrix.of e).det ≠ 0) => det_of_invEntries3 he
  refine hsmooth.congr fun e he => ?_
  rw [Function.comp_apply, smoothingOperator_apply,
    ← integral_mul_left_eq_self (fun k => φ (WhittakerBlock.archRealLift3 (invEntries3 e) * k) * F (g * k))
      (WhittakerBlock.archRealLift3 e)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [← archRealLift3_inv he, inv_mul_cancel_left, mul_assoc]

end ArchSmoothHelpers

section SmoothedMemberDocks

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

section ComponentBridges

open Matrix

noncomputable section

private theorem componentAt3_localToAdelic3_self
    (p : HeightOneSpectrum (𝓞 ℚ))
    (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ p (localToAdelic3 p x) = x := by
  apply Units.ext
  rw [componentAt3_coe, fin_localToAdelic3, mapMatrix_localMatN_self]

private theorem componentAt3_localToAdelic3_of_ne
    (p : HeightOneSpectrum (𝓞 ℚ))
    {q : HeightOneSpectrum (𝓞 ℚ)} (hq : q ≠ p) (x : LocalGL3 p) :
    componentAt3 (𝓞 ℚ) ℚ q (localToAdelic3 p x) = 1 := by
  apply Units.ext
  rw [componentAt3_coe, fin_localToAdelic3, mapMatrix_localMatN_of_ne (Fin 3) (𝓞 ℚ) ℚ p _ hq, Units.val_one]

end

end ComponentBridges

private theorem archEntries_one : Matrix.of (archEntries (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) = 1 := by
  rw [archEntries_eq, Units.val_one, map_one]

private theorem smoothingOperator_mem_cuspFunctions_of_isSmoothingKernel (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsSmoothingKernel φ) {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hF : F ∈ cuspFunctions ω a b Φ₀) :
    smoothingOperator φ F ∈ cuspFunctions ω a b Φ₀ := by
  obtain ⟨T, -, hT⟩ := exists_isCompactOperator_cuspidalSubspace_smoothingOperator ω a b Φ₀ hΦ₀
    exists_mul_eq_unipotent_mul_diagonal_mul_compact φ hφ
  obtain ⟨hRF, -⟩ := hT F hF
  exact hRF

private theorem isRightInvariant_and_isCosetEigenfunction_smoothingOperator_of_notMem
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (lam1 lam2 : HeightOneSpectrum (𝓞 ℚ) → ℂ) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : IsSmoothingKernel φ)
    (hφS : ∀ p, p ∉ S → ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, φ g ≠ 0 → componentAt3 (𝓞 ℚ) ℚ p g ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p)
    {F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hFc : Continuous F)
    (hK : ∀ p, p ∉ S → IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) F)
    (hT1 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen1 p)) F (lam1 p))
    (hT2 : ∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
      (localToAdelic3 p (heckeGen2 p)) F (lam2 p)) :
      (∀ p, p ∉ S →
        IsRightInvariant ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p)) (smoothingOperator φ F)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen1 p)) (smoothingOperator φ F) (lam1 p)) ∧
      (∀ p, p ∉ S → IsCosetEigenfunction ((localMaximalCompact3 (𝓞 ℚ) ℚ p).map (localToAdelic3 p))
        (localToAdelic3 p (heckeGen2 p)) (smoothingOperator φ F) (lam2 p)) := by
  have h := fun (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∉ S) =>
    isRightInvariant_and_isCosetEigenfunction_translateRight_smoothingOperator p (lam1 p) (lam2 p) φ hφ (hφS p hp) 1
      (map_one (componentAt3 (𝓞 ℚ) ℚ p)) F hFc (hK p hp) (hT1 p hp) (hT2 p hp)
  simp only [translateRight_one] at h
  exact ⟨fun p hp => (h p hp).1, fun p hp => (h p hp).2.1, fun p hp => (h p hp).2.2⟩

open Matrix in

private theorem isModerateGrowth3_of_forall_siegel_bound (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ)
    (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) {f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hf : f ∈ cuspFunctions ω a b Φ₀)
    (hb : ∀ c : ℝ, 0 < c → ∀ C : ℝ, ∃ K : ℝ, ∀ (n t k : AdelicGL 3 (𝓞 ℚ) ℚ)
        (_hx :
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p n = 1) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p t = 1) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) ∧
      ∀ w : InfinitePlace ℚ,
        (∀ i j : Fin 3,
          (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i i = 1 ∧
          (j < i → (archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
          ‖(archPlaceComponent3 ℚ w n : Matrix (Fin 3) (Fin 3) w.Completion) i j‖ ≤ C) ∧
        (∀ i j : Fin 3, i ≠ j →
          (archPlaceComponent3 ℚ w t : Matrix (Fin 3) (Fin 3) w.Completion) i j = 0) ∧
        c ≤ archRoot₁ ℚ w t ∧ c ≤ archRoot₂ ℚ w t ∧
        (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion)ᵀ *
            (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1),
      ∀ _w : InfinitePlace ℚ, ‖f (n * t * k)‖ ≤ K) :
    IsModerateGrowth3 ℚ f := by
  obtain ⟨c, C, hc, hcov⟩ := exists_mul_eq_unipotent_mul_diagonal_mul_compact
  obtain ⟨K, hK⟩ := hb c hc C
  refine isModerateGrowth3_of_bounded (F := ℚ) (C := K) fun g => ?_
  obtain ⟨γ, n, t, k, hg, hx⟩ := hcov g
  have hinv : f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g := ((mem_automorphicSubmodule_iff ω a b Φ₀ f).1 hf.1).1 γ g
  rw [← hinv, hg]
  exact hK n t k hx (InfinitePlace.mk (algebraMap ℚ ℂ))

private theorem archEntries_localToAdelic3 (v : HeightOneSpectrum (𝓞 ℚ)) (x : LocalGL3 v) :
    archEntries (localToAdelic3 v x) = archEntries 1 := by
  funext i j
  have h := congrFun (congrFun (arch_localToAdelic3 v x) i) j
  have h1 : (((1 : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 =
      (1 : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) i j := by
    rw [Units.val_one]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
      rfl
  show realCoordinate _ = realCoordinate _
  rw [h1, ← h]
  rfl

private theorem kernel_inv_localToAdelic3_mul {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    (v : HeightOneSpectrum (𝓞 ℚ)) {k : LocalGL3 v} (hk : k ∈ K' v) (y : AdelicGL 3 (𝓞 ℚ) ℚ) :
    φ ((localToAdelic3 v k)⁻¹ * y) = φ y := by
  rw [hφ, hφ]
  have harch : archEntries ((localToAdelic3 v k)⁻¹ * y) = archEntries y := by
    apply Matrix.of.injective
    rw [archEntries_mul, ← map_inv, archEntries_localToAdelic3, archEntries_one, one_mul]
  have hmem : ((localToAdelic3 v k)⁻¹ * y ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}) ↔
      (y ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}) := by
    simp only [Set.mem_setOf_eq]
    refine forall_congr' fun p => ?_
    rw [map_mul, map_inv]
    by_cases hp : p = v
    · subst hp
      rw [componentAt3_localToAdelic3_self]
      exact (K' p).mul_mem_cancel_left ((K' p).inv_mem hk)
    · rw [componentAt3_localToAdelic3_of_ne v hp, inv_one, one_mul]
  rw [harch]
  by_cases hy : y ∈ {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p}
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hmem.2 hy)]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy (hmem.1 h))]

private theorem smoothingOperator_mul_localToAdelic3 {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))} {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (v : HeightOneSpectrum (𝓞 ℚ)) {k : LocalGL3 v} (hk : k ∈ K' v)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    smoothingOperator φ F (g * localToAdelic3 v k) = smoothingOperator φ F g := by
  rw [smoothingOperator_apply, smoothingOperator_apply]
  have h := MeasureTheory.integral_mul_left_eq_self (μ := NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)
    (fun y => φ ((localToAdelic3 v k)⁻¹ * y) * F (g * y)) (localToAdelic3 v k)
  simp only [inv_mul_cancel_left, kernel_inv_localToAdelic3_mul hφ v hk] at h
  simpa only [mul_assoc] using h

private theorem forall_exists_openSubgroup_smoothingOperator {α : (Fin 3 → Fin 3 → ℝ) → ℂ}
    {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hopen : ∀ p, IsOpen (K' p : Set (GL (Fin 3) (p.adicCompletion ℚ)))) {φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}
    (hφ : ∀ g, φ g = α (archEntries g) *
      Set.indicator {x : AdelicGL 3 (𝓞 ℚ) ℚ | ∀ p, componentAt3 (𝓞 ℚ) ℚ p x ∈ K' p} (fun _ => (1 : ℂ)) g)
    (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ Uv : Subgroup (LocalGL3 v), IsOpen (Uv : Set (LocalGL3 v)) ∧
      ∀ k ∈ Uv, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, smoothingOperator φ F (g * localToAdelic3 v k) = smoothingOperator φ F g :=
  fun v => ⟨K' v, hopen v, fun _ hk g => smoothingOperator_mul_localToAdelic3 hφ F v hk g⟩

end SmoothedMemberDocks

section LocalGroupFacts

private theorem isOpen_localMaximalCompact3 (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) := by
  have h1 : ∀ i j : Fin 3, IsOpen {k : LocalGL3 p |
      Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1} := fun i j =>
    (Valued.isOpen_integer (p.adicCompletion ℚ)).preimage (Units.continuous_val.matrix_elem i j)
  have h2 : ∀ i j : Fin 3, IsOpen {k : LocalGL3 p |
      Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1} := fun i j =>
    (Valued.isOpen_integer (p.adicCompletion ℚ)).preimage (Units.continuous_coe_inv.matrix_elem i j)
  change IsOpen {k : LocalGL3 p |
    (∀ i j, Valued.v ((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1) ∧
      ∀ i j, Valued.v (((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j) ≤ 1}
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1 i j).inter
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h2 i j)

private theorem isOpen_setOf_valued_lt_one (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen {x : p.adicCompletion ℚ | Valued.v x < 1} := by
  have h := Valued.isOpen_ball (p.adicCompletion ℚ) 1
  convert h using 1
  ext x
  exact ⟨fun hx => (Valuation.restrict_lt_one_iff _).mpr hx, fun hx => (Valuation.restrict_lt_one_iff _).mp hx⟩

private theorem valued_sum_mul_lt_one {p : HeightOneSpectrum (𝓞 ℚ)} {s t : Fin 3 → p.adicCompletion ℚ}
    (hs : ∀ l, Valued.v (s l) < 1) (ht : ∀ l, Valued.v (t l) ≤ 1) : Valued.v (∑ l, s l * t l) < 1 := by
  refine Valuation.map_sum_lt _ one_ne_zero fun l _ => ?_
  rw [map_mul]
  calc Valued.v (s l) * Valued.v (t l) ≤ Valued.v (s l) * 1 := mul_le_mul_right (ht l) _
    _ = Valued.v (s l) := mul_one _
    _ < 1 := hs l

private abbrev IntegralScalar (p : HeightOneSpectrum (𝓞 ℚ)) : Type :=
  {c : (p.adicCompletion ℚ)ˣ // Valued.v (c : p.adicCompletion ℚ) ≤ 1}

private def IsCloseToOne (p : HeightOneSpectrum (𝓞 ℚ)) (c : IntegralScalar p)
    (m : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) : Prop :=
  ∀ i j, Valued.v (((c.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * (m - 1) i j) < 1

private theorem isCloseToOne_one (p : HeightOneSpectrum (𝓞 ℚ)) (c : IntegralScalar p) :
    IsCloseToOne p c 1 := by
  intro i j
  simp only [sub_self, Matrix.zero_apply, mul_zero, map_zero]
  exact zero_lt_one

private theorem isCloseToOne_mul {p : HeightOneSpectrum (𝓞 ℚ)} {c : IntegralScalar p}
    {a b : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)} (ha : IsCloseToOne p c a) (hb : IsCloseToOne p c b)
    (hb' : ∀ i j, Valued.v (b i j) ≤ 1) : IsCloseToOne p c (a * b) := by
  intro i j
  have hab : a * b - 1 = (a - 1) * b + (b - 1) := by rw [sub_mul, one_mul, sub_add_sub_cancel]
  rw [hab, Matrix.add_apply, mul_add, Matrix.mul_apply, Finset.mul_sum]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ (hb i j))
  simp only [← mul_assoc]
  exact valued_sum_mul_lt_one (fun l => ha i l) fun l => hb' l j

private def congruenceSubgroup (p : HeightOneSpectrum (𝓞 ℚ)) (c : IntegralScalar p) : Subgroup (LocalGL3 p) where
  carrier := {k | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧
    IsCloseToOne p c (k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) ∧
    IsCloseToOne p c ((k⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ))}
  one_mem' := ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ p).one_mem, by simpa using isCloseToOne_one p c,
    by simpa using isCloseToOne_one p c⟩
  mul_mem' := by
    rintro a b ⟨ha, ha1, ha2⟩ ⟨hb, hb1, hb2⟩
    refine ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ p).mul_mem ha hb, ?_, ?_⟩
    · rw [Units.val_mul]
      exact isCloseToOne_mul ha1 hb1 hb.1
    · rw [mul_inv_rev, Units.val_mul]
      exact isCloseToOne_mul hb2 ha2 ha.2
  inv_mem' := by
    rintro a ⟨ha, ha1, ha2⟩
    exact ⟨(localMaximalCompact3 (𝓞 ℚ) ℚ p).inv_mem ha, ha2, by simpa using ha1⟩

private theorem congruenceSubgroup_le (p : HeightOneSpectrum (𝓞 ℚ)) (c : IntegralScalar p) :
    congruenceSubgroup p c ≤ localMaximalCompact3 (𝓞 ℚ) ℚ p := fun _ hk => hk.1

private theorem isOpen_congruenceSubgroup (p : HeightOneSpectrum (𝓞 ℚ)) (c : IntegralScalar p) :
    IsOpen (congruenceSubgroup p c : Set (LocalGL3 p)) := by
  have hball : ∀ (f : LocalGL3 p → Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)), Continuous f →
      IsOpen {k | IsCloseToOne p c (f k)} := by
    intro f hf
    simp only [IsCloseToOne, Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact (isOpen_setOf_valued_lt_one p).preimage
      (continuous_const.mul ((hf.matrix_elem i j).sub continuous_const))
  change IsOpen {k : LocalGL3 p | k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ _ ∧ _}
  simp only [Set.setOf_and]
  exact (isOpen_localMaximalCompact3 p).inter
    ((hball _ Units.continuous_val).inter (hball _ Units.continuous_coe_inv))

private noncomputable def scalarMul {p : HeightOneSpectrum (𝓞 ℚ)} (c d : IntegralScalar p) : IntegralScalar p :=
  ⟨c.1 * d.1, by
    rw [Units.val_mul, map_mul]
    calc Valued.v (c.1 : p.adicCompletion ℚ) * Valued.v (d.1 : p.adicCompletion ℚ)
        ≤ Valued.v (c.1 : p.adicCompletion ℚ) * 1 := mul_le_mul_right d.2 _
      _ = Valued.v (c.1 : p.adicCompletion ℚ) := mul_one _
      _ ≤ 1 := c.2⟩

private theorem scalarMul_comm {p : HeightOneSpectrum (𝓞 ℚ)} (c d : IntegralScalar p) :
    scalarMul c d = scalarMul d c :=
  Subtype.ext (mul_comm _ _)

private theorem congruenceSubgroup_scalarMul_le_left (p : HeightOneSpectrum (𝓞 ℚ)) (c d : IntegralScalar p) :
    congruenceSubgroup p (scalarMul c d) ≤ congruenceSubgroup p c := by
  have key : ∀ m : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ), IsCloseToOne p (scalarMul c d) m →
      IsCloseToOne p c m := by
    intro m hm i j
    have h := hm i j
    have hrw : ((c.1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * (m - 1) i j =
        (d.1 : p.adicCompletion ℚ) *
          ((((scalarMul c d).1⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * (m - 1) i j) := by
      show _ = (d.1 : p.adicCompletion ℚ) * ((((c.1 * d.1)⁻¹ : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) * _)
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    rw [hrw, map_mul]
    calc Valued.v (d.1 : p.adicCompletion ℚ) * _ ≤ 1 * _ := mul_le_mul_left d.2 _
      _ = _ := one_mul _
      _ < 1 := h
  rintro k ⟨hk, hk1, hk2⟩
  exact ⟨hk, key _ hk1, key _ hk2⟩

private theorem congruenceSubgroup_scalarMul_le_right (p : HeightOneSpectrum (𝓞 ℚ)) (c d : IntegralScalar p) :
    congruenceSubgroup p (scalarMul c d) ≤ congruenceSubgroup p d := by
  rw [scalarMul_comm]
  exact congruenceSubgroup_scalarMul_le_left p d c

private theorem eq_one_of_forall_mem_congruenceSubgroup {p : HeightOneSpectrum (𝓞 ℚ)} {k : LocalGL3 p}
    (hk : ∀ c : IntegralScalar p, k ∈ congruenceSubgroup p c) : k = 1 := by
  apply Units.ext
  rw [Units.val_one, ← sub_eq_zero]
  ext i j : 1
  rw [Matrix.zero_apply]
  by_contra hx
  by_cases hlt : Valued.v (((k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) - 1) i j) < 1
  · have h := (hk ⟨Units.mk0 _ hx, hlt.le⟩).2.1 i j
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0, inv_mul_cancel₀ hx, map_one, lt_self_iff_false] at h
  · have h := (hk ⟨1, by simp⟩).2.1 i j
    simp only [inv_one, Units.val_one, one_mul] at h
    exact hlt h

private theorem exists_openCompactSubgroup_le_subset (p : HeightOneSpectrum (𝓞 ℚ)) {V : Set (LocalGL3 p)}
    (hV : V ∈ nhds (1 : LocalGL3 p)) :
    ∃ K' : Subgroup (LocalGL3 p), K' ≤ localMaximalCompact3 (𝓞 ℚ) ℚ p ∧ IsOpen (K' : Set (LocalGL3 p)) ∧
      IsCompact (K' : Set (LocalGL3 p)) ∧ (K' : Set (LocalGL3 p)) ⊆ V := by
  have hKc : IsCompact (localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) := isCompact_localMaximalCompact3 p
  have hC : IsCompact ((localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) \ interior V) := hKc.diff isOpen_interior
  have hclosed : ∀ c : IntegralScalar p, IsClosed (congruenceSubgroup p c : Set (LocalGL3 p)) := fun c =>
    (congruenceSubgroup p c).isClosed_of_isOpen (isOpen_congruenceSubgroup p c)
  have hdir : Directed (· ⊇ ·) fun c : IntegralScalar p => (congruenceSubgroup p c : Set (LocalGL3 p)) := by
    intro c d
    exact ⟨scalarMul c d, congruenceSubgroup_scalarMul_le_left p c d, congruenceSubgroup_scalarMul_le_right p c d⟩
  have hempty : ((localMaximalCompact3 (𝓞 ℚ) ℚ p : Set (LocalGL3 p)) \ interior V) ∩
      ⋂ c : IntegralScalar p, (congruenceSubgroup p c : Set (LocalGL3 p)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro k ⟨⟨-, hkV⟩, hk⟩
    rw [Set.mem_iInter] at hk
    have : k = 1 := eq_one_of_forall_mem_congruenceSubgroup fun c => hk c
    subst this
    exact hkV (mem_interior_iff_mem_nhds.mpr hV)
  haveI : Nonempty (IntegralScalar p) := ⟨⟨1, by simp⟩⟩
  obtain ⟨c, hc⟩ := hC.elim_directed_family_closed _ hclosed hempty hdir
  refine ⟨congruenceSubgroup p c, congruenceSubgroup_le p c, isOpen_congruenceSubgroup p c,
    hKc.of_isClosed_subset (hclosed c) (congruenceSubgroup_le p c), fun k hk => interior_subset ?_⟩
  by_contra hkV
  exact Set.eq_empty_iff_forall_notMem.mp hc k ⟨⟨congruenceSubgroup_le p c hk, hkV⟩, hk⟩

end LocalGroupFacts

section AdelicNeighbourhoods

open scoped Topology

section EntryBridges

open Matrix

noncomputable section

end

end EntryBridges

private theorem archEntries_inv (k : AdelicGL 3 (𝓞 ℚ) ℚ) :
    Matrix.of (archEntries (k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ)) = (Matrix.of (archEntries k))⁻¹ := by
  have h : Matrix.of (archEntries (k⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ)) * Matrix.of (archEntries k) = 1 := by
    rw [← archEntries_mul, inv_mul_cancel, archEntries_one]
  exact (Matrix.inv_eq_left_inv h).symm

private theorem exists_nhds_one_of_nhds_one_units {R : Type} [Monoid R] [TopologicalSpace R] {U : Set Rˣ}
    (hU : U ∈ 𝓝 (1 : Rˣ)) : ∃ W ∈ 𝓝 (1 : R), ∀ u : Rˣ, (u : R) ∈ W → ((u⁻¹ : Rˣ) : R) ∈ W → u ∈ U := by
  rw [(Units.isInducing_embedProduct (M := R)).nhds_eq_comap, Filter.mem_comap] at hU
  obtain ⟨t, ht, htU⟩ := hU
  rw [Units.embedProduct_apply, inv_one, Units.val_one, mem_nhds_prod_iff] at ht
  obtain ⟨W₁, hW₁, W₂, hW₂, hsub⟩ := ht
  refine ⟨W₁ ∩ MulOpposite.op ⁻¹' W₂, Filter.inter_mem hW₁ ?_, fun u hu hu' => ?_⟩
  · exact MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW₂
  · apply htU
    show Units.embedProduct R u ∈ t
    rw [Units.embedProduct_apply]
    exact hsub (Set.mk_mem_prod hu.1 hu'.2)

private theorem exists_forall_mem_nhds_of_mem_nhds_pi {ι : Type} {X : ι → Type} [∀ i, TopologicalSpace (X i)]
    {x : ∀ i, X i} {W : Set (∀ i, X i)} (hW : W ∈ 𝓝 x) :
    ∃ N : ∀ i, Set (X i), (∀ i, N i ∈ 𝓝 (x i)) ∧ ∀ y : ∀ i, X i, (∀ i, y i ∈ N i) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, N, hN, hsub⟩ := hW
  exact ⟨N, hN, fun y hy => hsub fun i _ => hy i⟩

private theorem exists_entry_nhds_of_mem_nhds {m : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)}
    {W : Set (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))} (hW : W ∈ 𝓝 m) :
    ∃ N : Fin 3 → Fin 3 → Set (AdeleRing (𝓞 ℚ) ℚ), (∀ i j, N i j ∈ 𝓝 (m i j)) ∧
      ∀ m' : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ), (∀ i j, m' i j ∈ N i j) → m' ∈ W := by
  obtain ⟨R, hR, hRW⟩ := exists_forall_mem_nhds_of_mem_nhds_pi (X := fun _ : Fin 3 => Fin 3 → AdeleRing (𝓞 ℚ) ℚ) hW
  choose N hN hNR using fun i => exists_forall_mem_nhds_of_mem_nhds_pi (X := fun _ : Fin 3 => AdeleRing (𝓞 ℚ) ℚ) (hR i)
  exact ⟨N, hN, fun m' hm' => hRW m' fun i => hNR i (m' i) (hm' i)⟩

private theorem exists_arch_fin_nhds_of_mem_nhds {x : AdeleRing (𝓞 ℚ) ℚ} {N : Set (AdeleRing (𝓞 ℚ) ℚ)} (hN : N ∈ 𝓝 x) :
    ∃ A ∈ 𝓝 x.1, ∃ Fs ∈ 𝓝 x.2, ∀ y : AdeleRing (𝓞 ℚ) ℚ, y.1 ∈ A → y.2 ∈ Fs → y ∈ N := by
  obtain ⟨A, hA, Fs, hFs, hsub⟩ := mem_nhds_prod_iff.1 (show N ∈ 𝓝 (x.1, x.2) from hN)
  exact ⟨A, hA, Fs, hFs, fun y hy hy' => hsub (Set.mk_mem_prod hy hy')⟩

private theorem isOpen_adicCompletionIntegers_rat (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ)) :=
  Valued.isOpen_valuationSubring (p.adicCompletion ℚ)

private theorem exists_finset_nhds_of_mem_nhds_finiteAdele {x : FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : ∀ p, x p ∈ p.adicCompletionIntegers ℚ) {Fs : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hFs : Fs ∈ 𝓝 x) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (O : ∀ p : HeightOneSpectrum (𝓞 ℚ), Set (p.adicCompletion ℚ)),
      (∀ p, O p ∈ 𝓝 (x p)) ∧ (∀ p, O p ⊆ p.adicCompletionIntegers ℚ) ∧
      ∀ y : FiniteAdeleRing (𝓞 ℚ) ℚ, (∀ p ∈ T, y p ∈ O p) → (∀ p, p ∉ T → y p ∈ p.adicCompletionIntegers ℚ) →
        y ∈ Fs := by
  let x' : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ := fun p => ⟨x p, hx p⟩
  have hFs' : Fs ∈ Filter.map
      (RestrictedProduct.structureMap (fun p : HeightOneSpectrum (𝓞 ℚ) => p.adicCompletion ℚ)
        (fun p => (p.adicCompletionIntegers ℚ : Set (p.adicCompletion ℚ))) Filter.cofinite) (𝓝 x') := by
    rw [(RestrictedProduct.isOpenEmbedding_structureMap
      (fun p => isOpen_adicCompletionIntegers_rat p)).map_nhds_eq x']
    exact hFs
  have hFs'' := Filter.mem_map.1 hFs'
  rw [nhds_pi, Filter.mem_pi] at hFs''
  obtain ⟨I, hI, t, ht, hsub⟩ := hFs''
  refine ⟨hI.toFinset, fun p => Subtype.val '' t p, fun p => ?_, fun p => ?_, fun y hyT hyI => ?_⟩
  · exact (isOpen_adicCompletionIntegers_rat p).isOpenMap_subtype_val.image_mem_nhds (ht p)
  · rintro _ ⟨z, -, rfl⟩
    exact z.2
  · have hy : ∀ p, y p ∈ p.adicCompletionIntegers ℚ := fun p => by
      by_cases hp : p ∈ I
      · obtain ⟨z, -, hz⟩ := hyT p (hI.mem_toFinset.2 hp)
        rw [← hz]
        exact z.2
      · exact hyI p (fun h => hp (hI.mem_toFinset.1 h))
    have hmem : (fun p : HeightOneSpectrum (𝓞 ℚ) => (⟨y p, hy p⟩ : p.adicCompletionIntegers ℚ)) ∈ I.pi t := by
      intro p hp
      obtain ⟨z, hz, hzy⟩ := hyT p (hI.mem_toFinset.2 hp)
      have : (⟨y p, hy p⟩ : p.adicCompletionIntegers ℚ) = z := Subtype.ext hzy.symm
      show (⟨y p, hy p⟩ : p.adicCompletionIntegers ℚ) ∈ t p
      rw [this]
      exact hz
    exact hsub hmem

private theorem localEntries_mem_nhds_one (p : HeightOneSpectrum (𝓞 ℚ))
    (O O' : Fin 3 → Fin 3 → Set (p.adicCompletion ℚ))
    (hO : ∀ i j, O i j ∈ 𝓝 ((1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j))
    (hO' : ∀ i j, O' i j ∈ 𝓝 ((1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j)) :
    {g : LocalGL3 p | (∀ i j, (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O i j) ∧
      ∀ i j, ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O' i j} ∈
        𝓝 (1 : LocalGL3 p) := by
  have hent : ∀ i j : Fin 3, Continuous fun g : LocalGL3 p => (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hinv : ∀ i j : Fin 3,
      Continuous fun g : LocalGL3 p => ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j :=
    fun i j => Units.continuous_coe_inv.matrix_elem i j
  have h1 : ∀ i j : Fin 3, {g : LocalGL3 p | (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O i j} ∈
      𝓝 (1 : LocalGL3 p) := fun i j =>
    (hent i j).continuousAt.preimage_mem_nhds (by simpa using hO i j)
  have h2 : ∀ i j : Fin 3, {g : LocalGL3 p | ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈
      O' i j} ∈ 𝓝 (1 : LocalGL3 p) := fun i j =>
    (hinv i j).continuousAt.preimage_mem_nhds (by simpa using hO' i j)
  have hA : {g : LocalGL3 p | ∀ i j, (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O i j} ∈
      𝓝 (1 : LocalGL3 p) := by
    have := Filter.iInter_mem.2 fun i : Fin 3 => Filter.iInter_mem.2 fun j : Fin 3 => h1 i j
    simpa only [Set.setOf_forall] using this
  have hB : {g : LocalGL3 p | ∀ i j, ((g⁻¹ : LocalGL3 p) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O' i j} ∈
      𝓝 (1 : LocalGL3 p) := by
    have := Filter.iInter_mem.2 fun i : Fin 3 => Filter.iInter_mem.2 fun j : Fin 3 => h2 i j
    simpa only [Set.setOf_forall] using this
  exact Filter.inter_mem hA hB

private theorem arch_entry_eq (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = realCoordinateHomeomorph.symm (archEntries k i j) := by
  have h1 : realCoordinateHomeomorph ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).1 = archEntries k i j :=
    realCoordinateHomeomorph_apply _
  rw [← h1, Homeomorph.symm_apply_apply]

private theorem fin_entry_eq (p : HeightOneSpectrum (𝓞 ℚ)) (k : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3) :
    ((k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p =
      (componentAt3 (𝓞 ℚ) ℚ p k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j := by
  rw [coe_componentAt3]
  rfl

private theorem continuousAt_invArray_one :
    ContinuousAt (fun m : Fin 3 → Fin 3 → ℝ => Matrix.of.symm (Matrix.of m)⁻¹) (Matrix.of.symm 1) := by
  have h : ContinuousAt (Inv.inv : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ) 1 :=
    continuousAt_matrix_inv 1 (by simp)
  exact h.comp (f := fun m : Fin 3 → Fin 3 → ℝ => Matrix.of m) (by exact continuousAt_id)

private theorem fin_one_entry (p : HeightOneSpectrum (𝓞 ℚ)) (i j : Fin 3) :
    ((1 : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p =
      (1 : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j := by
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]
    rfl

private theorem exists_nhds_archEntries_finset_of_nhds_one {U : Set (AdelicGL 3 (𝓞 ℚ) ℚ)}
    (hU : U ∈ 𝓝 (1 : AdelicGL 3 (𝓞 ℚ) ℚ)) :
    ∃ B ∈ 𝓝 (archEntries 1), ∃ (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (V : ∀ p, Set (LocalGL3 p)),
      (∀ p, V p ∈ 𝓝 1) ∧ ∀ k, archEntries k ∈ B → (∀ p ∈ T, componentAt3 (𝓞 ℚ) ℚ p k ∈ V p) →
        (∀ p, p ∉ T → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) → k ∈ U := by
  classical
  obtain ⟨W, hW, hWU⟩ := exists_nhds_one_of_nhds_one_units hU
  obtain ⟨N, hN, hNW⟩ := exists_entry_nhds_of_mem_nhds (m := 1) (by simpa using hW)
  choose A hA Fs hFs hAFs using fun i j => exists_arch_fin_nhds_of_mem_nhds (hN i j)
  have hint : ∀ i j : Fin 3, ∀ p : HeightOneSpectrum (𝓞 ℚ),
      ((1 : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) i j).2 p ∈ p.adicCompletionIntegers ℚ := by
    intro i j p
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.one_apply_eq]
      exact one_mem _
    · simp only [Matrix.one_apply_ne hij]
      exact zero_mem _
  choose T O hO hOint hTO using fun i j => exists_finset_nhds_of_mem_nhds_finiteAdele (hint i j) (hFs i j)

  let B₀ : Set (Fin 3 → Fin 3 → ℝ) := {m | ∀ i j, realCoordinateHomeomorph.symm (m i j) ∈ A i j}
  have hB₀ : B₀ ∈ 𝓝 (archEntries 1) := by
    have : ∀ i j : Fin 3,
        {m : Fin 3 → Fin 3 → ℝ | realCoordinateHomeomorph.symm (m i j) ∈ A i j} ∈ 𝓝 (archEntries 1) := by
      intro i j
      refine (realCoordinateHomeomorph.symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))
        ).continuousAt.preimage_mem_nhds ?_
      simpa only [Function.comp, ← arch_entry_eq, Units.val_one] using hA i j
    have := Filter.iInter_mem.2 fun i : Fin 3 => Filter.iInter_mem.2 fun j : Fin 3 => this i j
    simpa only [B₀, Set.setOf_forall] using this
  have hone : archEntries (1 : AdelicGL 3 (𝓞 ℚ) ℚ) = Matrix.of.symm 1 := by
    rw [Equiv.eq_symm_apply, archEntries_one]
  have hB₁ : (fun m : Fin 3 → Fin 3 → ℝ => Matrix.of.symm (Matrix.of m)⁻¹) ⁻¹' B₀ ∈ 𝓝 (archEntries 1) := by
    have hc : ContinuousAt (fun m : Fin 3 → Fin 3 → ℝ => Matrix.of.symm (Matrix.of m)⁻¹) (archEntries 1) := by
      rw [hone]
      exact continuousAt_invArray_one
    refine hc.preimage_mem_nhds ?_
    simpa only [hone, Equiv.apply_symm_apply, inv_one] using hB₀

  let T₀ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
    Finset.univ.biUnion fun i : Fin 3 => Finset.univ.biUnion fun j : Fin 3 => T i j
  have hT₀ : ∀ (i j : Fin 3) (p : HeightOneSpectrum (𝓞 ℚ)), p ∈ T i j → p ∈ T₀ := fun i j p hp => by
    simp only [T₀, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, j, hp⟩
  let V : ∀ p : HeightOneSpectrum (𝓞 ℚ), Set (GL (Fin 3) (p.adicCompletion ℚ)) := fun p =>
    {g | (∀ i j, (g : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O i j p) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 3) (p.adicCompletion ℚ)) : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) i j ∈ O i j p}
  have hV : ∀ p, V p ∈ 𝓝 (1 : GL (Fin 3) (p.adicCompletion ℚ)) := fun p =>
    localEntries_mem_nhds_one p (fun i j => O i j p) (fun i j => O i j p)
      (fun i j => by simpa only [fin_one_entry] using hO i j p)
      (fun i j => by simpa only [fin_one_entry] using hO i j p)

  have key : ∀ k : AdelicGL 3 (𝓞 ℚ) ℚ, archEntries k ∈ B₀ →
      (∀ p ∈ T₀, (componentAt3 (𝓞 ℚ) ℚ p k : Matrix (Fin 3) (Fin 3) (p.adicCompletion ℚ)) ∈
        {m | ∀ i j, m i j ∈ O i j p}) →
      (∀ p, p ∉ T₀ → componentAt3 (𝓞 ℚ) ℚ p k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ p) →
      (k : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) ∈ W := by
    intro k hB hT hK
    refine hNW _ fun i j => hAFs i j _ ?_ ?_
    · rw [arch_entry_eq]
      exact hB i j
    · refine hTO i j _ (fun p hp => ?_) (fun p hp => ?_)
      · rw [fin_entry_eq]
        exact hT p (hT₀ i j p hp) i j
      · rw [fin_entry_eq]
        by_cases hp₀ : p ∈ T₀
        · exact hOint i j p (hT p hp₀ i j)
        · exact (hK p hp₀).1 i j
  refine ⟨B₀ ∩ (fun m => Matrix.of.symm (Matrix.of m)⁻¹) ⁻¹' B₀, Filter.inter_mem hB₀ hB₁, T₀, V, hV,
    fun k hkB hkT hkK => hWU k ?_ ?_⟩
  · exact key k hkB.1 (fun p hp => (hkT p hp).1) hkK
  · refine key k⁻¹ ?_ (fun p hp => ?_) (fun p hp => ?_)
    · have := hkB.2
      simpa only [Set.mem_preimage, ← archEntries_inv, Equiv.symm_apply_apply] using this
    · show ∀ i j, _
      rw [map_inv]
      exact (hkT p hp).2
    · rw [map_inv]
      exact (localMaximalCompact3 (𝓞 ℚ) ℚ p).inv_mem (hkK p hp)

end AdelicNeighbourhoods

end SmoothedMember

end LanglandsTunnell.CubicInduction

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace R1CuspDeriv

open MeasureTheory Filter Metric Topology
open IsDedekindDomain NumberField AutomorphicForm
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.LanglandsTunnell.CubicInduction"

section Engine

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable (ν : Measure X) [IsFiniteMeasure ν] {C : Set X}

theorem integrable_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C) (φ : X → ℂ)
    (hφ : Continuous φ) : Integrable φ ν := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hφ.continuousOn
  exact Integrable.of_bound hφ.aestronglyMeasurable M (hνC.mono fun y hy => hM y hy)

theorem continuous_integral_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C)
    {P : Type*} [TopologicalSpace P] [LocallyCompactSpace P] [FirstCountableTopology P]
    (f : P → X → ℂ) (hf : Continuous fun q : P × X => f q.1 q.2) :
    Continuous fun p => ∫ y, f p y ∂ν := by
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨N, hN, hNp⟩ := exists_compact_mem_nhds p₀
  obtain ⟨M, hM⟩ := (hN.prod hC).exists_bound_of_continuousOn hf.continuousOn
  have hcont : ∀ p : P, Continuous fun y => f p y := fun p =>
    hf.comp (continuous_const.prodMk continuous_id)
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Eventually.of_forall fun p => (hcont p).aestronglyMeasurable
  · filter_upwards [hNp] with p hp
    exact hνC.mono fun y hy => hM (p, y) ⟨hp, hy⟩
  · exact ae_of_all _ fun y => (hf.comp (continuous_id.prodMk continuous_const)).continuousAt

theorem hasDerivAt_integral_of_continuous (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν, y ∈ C)
    (F F' : ℝ → X → ℂ) {r : ℝ} (hr : 0 < r)
    (hF : Continuous fun q : closedBall (0 : ℝ) r × X => F q.1 q.2)
    (hF' : Continuous fun q : closedBall (0 : ℝ) r × X => F' q.1 q.2)
    (hd : ∀ y, ∀ s ∈ ball (0 : ℝ) r, HasDerivAt (fun σ => F σ y) (F' s y) s) :
    ∀ s₀ ∈ ball (0 : ℝ) r, HasDerivAt (fun s => ∫ y, F s y ∂ν) (∫ y, F' s₀ y ∂ν) s₀ := by
  intro s₀ hs₀
  haveI : CompactSpace (closedBall (0 : ℝ) r) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := (isCompact_univ.prod hC).exists_bound_of_continuousOn hF'.continuousOn
  have hcF : ∀ s (hs : s ∈ closedBall (0 : ℝ) r), Continuous fun y => F s y := fun s hs =>
    hF.comp ((continuous_const (y := (⟨s, hs⟩ : closedBall (0 : ℝ) r))).prodMk continuous_id)
  have hcF' : ∀ s (hs : s ∈ closedBall (0 : ℝ) r), Continuous fun y => F' s y := fun s hs =>
    hF'.comp ((continuous_const (y := (⟨s, hs⟩ : closedBall (0 : ℝ) r))).prodMk continuous_id)
  have hball : ball (0 : ℝ) r ∈ 𝓝 s₀ := isOpen_ball.mem_nhds hs₀
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (F' := F') (x₀ := s₀)
    (bound := fun _ => M) hball ?_ ?_ ?_ ?_ (integrable_const M) ?_).2
  · filter_upwards [hball] with s hs using (hcF s (ball_subset_closedBall hs)).aestronglyMeasurable
  · exact integrable_of_continuous ν hC hνC _ (hcF s₀ (ball_subset_closedBall hs₀))
  · exact (hcF' s₀ (ball_subset_closedBall hs₀)).aestronglyMeasurable
  · exact hνC.mono fun y hy s hs => hM (⟨s, ball_subset_closedBall hs⟩, y) ⟨Set.mem_univ _, hy⟩
  · exact ae_of_all _ fun y s hs => hd y s hs

end Engine

section Arch

def ofRealHom : ℝ →+* InfiniteAdeleRing ℚ :=
  RingHom.pi fun v => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)).symm.toRingHom

theorem ofRealHom_apply (r : ℝ) : ofRealHom r = StandardKernel.ofReal r := rfl

theorem realCoord_ofReal (r : ℝ) : StandardKernel.realCoord (StandardKernel.ofReal r) = r := by
  show (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
    ((InfinitePlace.Completion.ringEquivRealOfIsReal _).symm r) = r
  exact RingEquiv.apply_symm_apply _ _

def rho : Matrix (Fin 3) (Fin 3) ℝ →+* Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ) := ofRealHom.mapMatrix

def psi : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) →+* Matrix (Fin 3) (Fin 3) ℝ :=
  (StandardKernel.realCoord.comp (AdelicLevel.adeleArch (𝓞 ℚ) ℚ)).mapMatrix

theorem archRealMat3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) :
    WhittakerBlock.archRealMat3 e = archMatrixInclN (Fin 3) ℚ (rho e) := rfl

theorem psi_archRealMat3 (e : Matrix (Fin 3) (Fin 3) ℝ) : psi (WhittakerBlock.archRealMat3 e) = e := by
  ext i j
  change StandardKernel.realCoord (AdelicLevel.adeleArch (𝓞 ℚ) ℚ (archMatrixInclN (Fin 3) ℚ (rho e) i j)) = e i j
  rw [adeleArch_archMatrixInclN]
  exact realCoord_ofReal (e i j)

theorem isUnit_archRealMat3_iff (e : Matrix (Fin 3) (Fin 3) ℝ) :
    IsUnit (WhittakerBlock.archRealMat3 e) ↔ e.det ≠ 0 := by
  constructor
  · intro h
    have h' := h.map psi
    rw [psi_archRealMat3, Matrix.isUnit_iff_isUnit_det] at h'
    exact h'.ne_zero
  · intro h
    have hu : IsUnit e := (Matrix.isUnit_iff_isUnit_det e).mpr (isUnit_iff_ne_zero.mpr h)
    exact hu.map ((archMatrixInclHomN (Fin 3) ℚ).comp rho.toMonoidHom)

def liftGL : GL (Fin 3) ℝ →* AdelicGL 3 (𝓞 ℚ) ℚ := (archInclN (Fin 3) ℚ).comp (Units.map rho.toMonoidHom)

def toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : GL (Fin 3) ℝ :=
  Matrix.nonsingInvUnit e (isUnit_iff_ne_zero.mpr h)

@[scoped simp] theorem coe_toGL (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) : (toGL e h : Matrix (Fin 3) (Fin 3) ℝ) = e :=
  rfl

theorem archRealLift3_eq (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    WhittakerBlock.archRealLift3 e = liftGL (toGL e h) := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_pos ((isUnit_archRealMat3_iff e).mpr h)]
  exact Units.ext (by rw [IsUnit.unit_spec]; rfl)

theorem archRealLift3_of_det (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det = 0) : WhittakerBlock.archRealLift3 e = 1 := by
  unfold WhittakerBlock.archRealLift3
  rw [dif_neg]
  rw [isUnit_archRealMat3_iff]
  exact fun h' => h' h

theorem coe_archRealLift3 (e : Matrix (Fin 3) (Fin 3) ℝ) (h : e.det ≠ 0) :
    ((WhittakerBlock.archRealLift3 e : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      WhittakerBlock.archRealMat3 e := by
  rw [archRealLift3_eq e h]; rfl

theorem archRealLift3_mul (e e' : Fin 3 → Fin 3 → ℝ) (h : (Matrix.of e).det ≠ 0) (h' : (Matrix.of e').det ≠ 0) :
    WhittakerBlock.archRealLift3 (Matrix.of e * Matrix.of e') =
      WhittakerBlock.archRealLift3 e * WhittakerBlock.archRealLift3 e' := by
  have hm : (Matrix.of e * Matrix.of e').det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero h h'
  have h1 : WhittakerBlock.archRealLift3 e = liftGL (toGL (Matrix.of e) h) := archRealLift3_eq (Matrix.of e) h
  have h2 : WhittakerBlock.archRealLift3 e' = liftGL (toGL (Matrix.of e') h') := archRealLift3_eq (Matrix.of e') h'
  rw [archRealLift3_eq _ hm, h1, h2, ← map_mul liftGL]
  congr 1
  exact Units.ext rfl

theorem archRealLift3_one : WhittakerBlock.archRealLift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  rw [archRealLift3_eq _ (by simp)]
  have : toGL 1 (by simp) = 1 := Units.ext rfl
  rw [this, map_one]

theorem commute_archInclN (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : t * archInclN (Fin 3) ℚ h = archInclN (Fin 3) ℚ h * t := by
  set A : AdelicGL 3 (𝓞 ℚ) ℚ := archInclN (Fin 3) ℚ h with hAdef
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  have hA1 : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) =
      (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) :=
    Matrix.ext fun a b => adeleArch_archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b
  have hA2 : (AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 :=
    Matrix.ext fun a b => adeleFin_archMatrixInclN (Fin 3) ℚ (h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b
  have hT : (AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) = 1 := by
    rw [← Units.val_one, ← ht]; rfl
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · change ((AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j =
      ((AdelicLevel.adeleArch (𝓞 ℚ) ℚ).mapMatrix
        ((A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j
    rw [map_mul, map_mul, hA1, hT, one_mul, mul_one]
  · change ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        ((t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j =
      ((AdelicLevel.adeleFin (𝓞 ℚ) ℚ).mapMatrix
        ((A : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) * (t : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)))) i j
    rw [map_mul, map_mul, hA2, one_mul, mul_one]

theorem commute_archRealLift3 (t : AdelicGL 3 (𝓞 ℚ) ℚ) (ht : archComponent3 (𝓞 ℚ) ℚ t = 1)
    (e : Matrix (Fin 3) (Fin 3) ℝ) :
    t * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t := by
  by_cases h : e.det = 0
  · rw [archRealLift3_of_det e h, mul_one, one_mul]
  · rw [archRealLift3_eq e h]
    exact commute_archInclN t ht _

def cfun (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0

def efun (i j : Fin 3) : Fin 3 → Fin 3 → ℝ := fun a b => if a = i ∧ b = j then 1 else 0

def kap (i j : Fin 3) (s : ℝ) : ℝ := 1 + if i = j then s else 0

theorem cfun_eq (i j : Fin 3) (s : ℝ) : cfun i j s = (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j := by
  funext a b
  simp only [cfun, efun, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

theorem of_cfun (i j : Fin 3) (s : ℝ) : Matrix.of (cfun i j s) = 1 + s • Matrix.single i j (1 : ℝ) := by
  ext a b
  simp only [cfun, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  by_cases h : a = i ∧ b = j
  · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

theorem det_cfun (i j : Fin 3) (s : ℝ) : (Matrix.of (cfun i j s)).det = kap i j s := by
  unfold cfun kap
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three]

theorem kap_pos (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : 0 < kap i j s := by
  unfold kap
  split_ifs
  · have := (abs_lt.mp hs).1; linarith
  · norm_num

theorem continuous_kap (i j : Fin 3) : Continuous (kap i j) := by
  by_cases h : i = j
  · have : kap i j = fun s => 1 + s := funext fun s => by simp [kap, h]
    rw [this]; fun_prop
  · have : kap i j = fun _ => 1 := funext fun s => by simp [kap, h]
    rw [this]; fun_prop

theorem det_cfun_ne (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : (Matrix.of (cfun i j s)).det ≠ 0 := by
  rw [det_cfun]; exact (kap_pos i j hs).ne'

theorem cfun_zero (i j : Fin 3) : Matrix.of (cfun i j 0) = 1 := by
  rw [of_cfun, zero_smul, add_zero]

theorem of_cfun_mul (i j : Fin 3) (s τ : ℝ) :
    Matrix.of (cfun i j s) * Matrix.of (cfun i j τ) = Matrix.of (cfun i j (s + kap i j s * τ)) := by
  rw [of_cfun, of_cfun, of_cfun]
  by_cases h : i = j
  · subst h
    have hE : Matrix.single i i (1 : ℝ) * Matrix.single i i (1 : ℝ) = Matrix.single i i (1 : ℝ) := by
      rw [Matrix.single_mul_single_same, one_mul]
    have hk : kap i i s = 1 + s := by simp [kap]
    rw [hk, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hE, smul_smul]
    module
  · have hE : Matrix.single i j (1 : ℝ) * Matrix.single i j (1 : ℝ) = 0 :=
      Matrix.single_mul_single_of_ne 1 i j i (Ne.symm h) 1
    have hk : kap i j s = 1 := by simp [kap, h]
    rw [hk, add_mul, mul_add, mul_add, one_mul, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, hE]
    module

theorem continuous_cfun (i j : Fin 3) : Continuous (cfun i j) := by
  rw [show cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j from funext (cfun_eq i j)]
  fun_prop

theorem hasDerivAt_cfun (i j : Fin 3) (s : ℝ) : HasDerivAt (cfun i j) (efun i j) s := by
  rw [show cfun i j = fun s => (fun a b => if a = b then (1 : ℝ) else 0) + s • efun i j from funext (cfun_eq i j)]
  have h := ((hasDerivAt_id s).smul_const (efun i j)).const_add (fun a b : Fin 3 => if a = b then (1 : ℝ) else 0)
  rw [one_smul] at h
  exact h

def U : Set (Fin 3 → Fin 3 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem isOpen_U : IsOpen U := by
  have hc : Continuous fun e : Fin 3 → Fin 3 → ℝ => (Matrix.of e).det :=
    (continuous_id : Continuous fun e : Fin 3 → Fin 3 → ℝ => Matrix.of e).matrix_det
  exact isOpen_compl_singleton.preimage hc

theorem cfun_mem_U (i j : Fin 3) {s : ℝ} (hs : |s| < 1) : cfun i j s ∈ U := det_cfun_ne i j hs

def L (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (cfun i j s)

theorem L_zero (i j : Fin 3) : L i j 0 = 1 := by
  show WhittakerBlock.archRealLift3 (Matrix.of (cfun i j 0)) = 1
  rw [cfun_zero]
  exact archRealLift3_one

theorem L_mul_L (i j : Fin 3) {s τ : ℝ} (hs : |s| < 1) (hτ : |τ| < 1) :
    L i j s * L i j τ = L i j (s + kap i j s * τ) := by
  have h := archRealLift3_mul (cfun i j s) (cfun i j τ) (det_cfun_ne i j hs) (det_cfun_ne i j hτ)
  rw [of_cfun_mul] at h
  exact h.symm

theorem archDeriv_apply (i j : Fin 3) (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    WhittakerBlock.archDeriv i j φ g = deriv (fun s => φ (g * L i j s)) 0 := rfl

variable {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ}

theorem differentiableAt_slice (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ U) :
    DifferentiableAt ℝ (fun e : Fin 3 → Fin 3 → ℝ => Φ (h * WhittakerBlock.archRealLift3 e)) e :=
  ((hΦ h).differentiableOn (by simp)).differentiableAt (isOpen_U.mem_nhds he)

theorem differentiableAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) : DifferentiableAt ℝ (fun σ => Φ (h * L i j σ)) s :=
  (differentiableAt_slice hΦ h (cfun_mem_U i j hs)).comp s (hasDerivAt_cfun i j s).differentiableAt

theorem archDeriv_apply_mul_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    WhittakerBlock.archDeriv i j Φ (h * L i j s) = (kap i j s : ℂ) * deriv (fun σ => Φ (h * L i j σ)) s := by
  rw [archDeriv_apply]

  have hev : (fun τ => Φ (h * L i j s * L i j τ)) =ᶠ[𝓝 0] fun τ => (fun σ => Φ (h * L i j σ)) (s + kap i j s * τ) := by
    have hnb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with τ hτ
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    rw [mul_assoc, L_mul_L i j hs hτ']
  rw [hev.deriv_eq]
  rw [show (fun τ => (fun σ => Φ (h * L i j σ)) (s + kap i j s * τ)) =
      fun τ => (fun σ' => (fun σ => Φ (h * L i j σ)) (s + σ')) (kap i j s * τ) from rfl]
  rw [deriv_comp_mul_left (kap i j s) (fun σ' => (fun σ => Φ (h * L i j σ)) (s + σ')) 0, mul_zero,
    deriv_comp_const_add (fun σ => Φ (h * L i j σ)) s 0, add_zero, Complex.real_smul]

theorem hasDerivAt_comp_L (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (h : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (fun σ => Φ (h * L i j σ)) ((kap i j s : ℂ)⁻¹ * WhittakerBlock.archDeriv i j Φ (h * L i j s)) s := by
  have hk : (kap i j s : ℂ) ≠ 0 := by exact_mod_cast (kap_pos i j hs).ne'
  rw [archDeriv_apply_mul_L hΦ h i j hs, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  exact (differentiableAt_comp_L hΦ h i j hs).hasDerivAt

def mulE (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a b => (Matrix.of e * Matrix.single i j (1 : ℝ)) a b

theorem mulE_eq (i j : Fin 3) : mulE i j = fun e a b => if b = j then e a i else 0 := by
  funext e a b
  simp only [mulE, Matrix.mul_apply, Matrix.of_apply, Matrix.single_apply, mul_ite, mul_one, mul_zero]
  by_cases hb : b = j
  · rw [if_pos hb, Finset.sum_eq_single i (fun k _ hk => if_neg (fun h => hk h.1.symm)) (by simp)]
    rw [if_pos ⟨rfl, hb.symm⟩]
  · rw [if_neg hb]
    exact Finset.sum_eq_zero fun k _ => if_neg fun h => hb h.2.symm

theorem contDiff_mulE (i j : Fin 3) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mulE i j) := by
  rw [mulE_eq]
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  by_cases hb : b = j
  · simp only [if_pos hb]; exact contDiff_apply_apply ℝ ℝ a i
  · simp only [if_neg hb]; exact contDiff_const

theorem of_mul_of_cfun (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) (τ : ℝ) :
    Matrix.of e * Matrix.of (cfun i j τ) = Matrix.of (e + τ • mulE i j e) := by
  rw [of_cfun, mul_add, mul_one, Matrix.mul_smul]
  rfl

theorem hasDerivAt_mul_cfun (i j : Fin 3) (e : Fin 3 → Fin 3 → ℝ) :
    HasDerivAt (fun τ : ℝ => e + τ • mulE i j e) (mulE i j e) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (mulE i j e)).const_add e
  rw [one_smul] at h
  exact h

theorem archDeriv_slice_eq (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (i j : Fin 3)
    {e : Fin 3 → Fin 3 → ℝ} (he : e ∈ U) :
    WhittakerBlock.archDeriv i j Φ (g * WhittakerBlock.archRealLift3 e) =
      fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) e (mulE i j e) := by
  rw [archDeriv_apply]
  have hev : (fun τ => Φ (g * WhittakerBlock.archRealLift3 e * L i j τ)) =ᶠ[𝓝 0]
      (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) ∘ fun τ => e + τ • mulE i j e := by
    have hnb : ball (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := isOpen_ball.mem_nhds (by simp)
    filter_upwards [hnb] with τ hτ
    have hτ' : |τ| < 1 := by simpa [Real.dist_eq] using hτ
    simp only [Function.comp_apply, L]
    rw [mul_assoc, ← archRealLift3_mul e (cfun i j τ) he (det_cfun_ne i j hτ'), of_mul_of_cfun]
    rfl
  rw [hev.deriv_eq]
  exact ((differentiableAt_slice hΦ g he).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
    (hasDerivAt_mul_cfun i j e) (by simp)).deriv

theorem isArchSmooth3_archDeriv (hΦ : WhittakerBlock.IsArchSmooth3 Φ) (i j : Fin 3) :
    WhittakerBlock.IsArchSmooth3 (WhittakerBlock.archDeriv i j Φ) := by
  intro g
  have hψ := hΦ g
  have hU : {e : Fin 3 → Fin 3 → ℝ | (Matrix.of e).det ≠ 0} = U := rfl
  rw [hU] at hψ ⊢
  have hd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun e => fderiv ℝ (fun e' : Fin 3 → Fin 3 → ℝ => Φ (g * WhittakerBlock.archRealLift3 e')) e (mulE i j e))
      U :=
    (hψ.fderiv_of_isOpen isOpen_U (by simp)).clm_apply (contDiff_mulE i j).contDiffOn
  exact hd.congr fun e he => archDeriv_slice_eq hΦ g i j he

theorem continuous_archRealMat3_cfun (i j : Fin 3) :
    Continuous fun s => WhittakerBlock.archRealMat3 (cfun i j s) := by
  have h1 : Continuous fun s => rho (Matrix.of (cfun i j s)) :=
    (continuous_cfun i j).matrix_map StandardKernel.continuous_ofReal
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact ((continuous_apply_apply a b).comp h1).prodMk continuous_const

theorem abs_neg_div_kap_lt (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 3) : |-(s / kap i j s)| < 1 := by
  have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hk := kap_pos i j hs1
  rw [abs_neg, abs_div, abs_of_pos hk, div_lt_one hk]
  unfold kap
  split_ifs with h
  · have := (abs_le.mp hs).1; have := (abs_le.mp hs).2
    rw [abs_lt]; constructor <;> linarith
  · simpa using hs1

theorem L_inv_eq (i j : Fin 3) {s : ℝ} (hs : |s| ≤ 1 / 3) :
    (L i j s)⁻¹ = L i j (-(s / kap i j s)) := by
  have hs1 : |s| < 1 := lt_of_le_of_lt hs (by norm_num)
  have hk := kap_pos i j hs1
  rw [inv_eq_iff_mul_eq_one, L_mul_L i j hs1 (abs_neg_div_kap_lt i j hs)]
  have : s + kap i j s * -(s / kap i j s) = 0 := by field_simp; ring
  rw [this, L_zero]

theorem continuousOn_L (i j : Fin 3) : ContinuousOn (L i j) (closedBall (0 : ℝ) (1 / 3)) := by
  rw [continuousOn_iff_continuous_restrict]
  have hmem : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| ≤ 1 / 3 := fun s => by
    have := s.2; simpa [Real.dist_eq] using this
  have hmem1 : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| < 1 := fun s => lt_of_le_of_lt (hmem s) (by norm_num)
  rw [Units.continuous_iff]
  constructor
  · have : (Units.val ∘ (closedBall (0 : ℝ) (1 / 3)).domRestrict (L i j)) =
        fun s : closedBall (0 : ℝ) (1 / 3) => WhittakerBlock.archRealMat3 (cfun i j s) := by
      funext s
      exact coe_archRealLift3 _ (det_cfun_ne i j (hmem1 s))
    rw [this]
    exact (continuous_archRealMat3_cfun i j).comp continuous_subtype_val
  · have : (fun s : closedBall (0 : ℝ) (1 / 3) => Units.val (((closedBall (0 : ℝ) (1 / 3)).domRestrict (L i j) s)⁻¹)) =
        fun s : closedBall (0 : ℝ) (1 / 3) => WhittakerBlock.archRealMat3 (cfun i j (-(s / kap i j s))) := by
      funext s
      show Units.val (L i j s)⁻¹ = _
      rw [L_inv_eq i j (hmem s)]
      exact coe_archRealLift3 _ (det_cfun_ne i j (abs_neg_div_kap_lt i j (hmem s)))
    rw [this]
    refine (continuous_archRealMat3_cfun i j).comp ?_
    have hk : ∀ s : closedBall (0 : ℝ) (1 / 3), kap i j s ≠ 0 := fun s => (kap_pos i j (hmem1 s)).ne'
    have hkc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => kap i j s :=
      (continuous_kap i j).comp continuous_subtype_val
    exact (continuous_subtype_val.div hkc hk).neg

end Arch

section Cusp

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

def ν0 : Measure (AdeleRing (𝓞 ℚ) ℚ) :=
  ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (AdelicBox.adelicBox ℚ)

scoped instance : IsProbabilityMeasure ν0 := AdelicBox.isProbabilityMeasure_cond_adelicBox ℚ

scoped instance : SecondCountableTopology (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdeleRing.secondCountableTopology ℚ

theorem exists_compact_ae : ∃ C : Set (AdeleRing (𝓞 ℚ) ℚ), IsCompact C ∧ ∀ᵐ y ∂ν0, y ∈ C := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset ℚ
  exact ⟨C, hC, (ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox ℚ)).mono fun y hy => hsub hy⟩

variable (u : AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ)
  (hu : Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => u p.1 p.2)

include hu

theorem integral_integral_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ x, ∫ y, (∑ i, c i * f (u x y * g * t i)) ∂ν0 ∂ν0 = ∑ i, c i * ∫ x, ∫ y, f (u x y * (g * t i)) ∂ν0 ∂ν0 := by
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae
  have hjc : ∀ i, Continuous fun q : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => f (u q.1 q.2 * (g * t i)) :=
    fun i => hc.comp (hu.mul continuous_const)
  have hin : ∀ i x, Integrable (fun y => f (u x y * (g * t i))) ν0 := fun i x =>
    integrable_of_continuous ν0 hC hνC _ (hc.comp ((hu.comp (Continuous.prodMk_right x)).mul continuous_const))
  have hout : ∀ i, Integrable (fun x => ∫ y, f (u x y * (g * t i)) ∂ν0) ν0 := fun i =>
    integrable_of_continuous ν0 hC hνC _ (continuous_integral_of_continuous ν0 hC hνC _ (hjc i))
  have hinner : ∀ x, ∫ y, (∑ i, c i * f (u x y * g * t i)) ∂ν0 = ∑ i, c i * ∫ y, f (u x y * (g * t i)) ∂ν0 := by
    intro x
    simp_rw [mul_assoc]
    rw [integral_finsetSum _ fun i _ => (hin i x).const_mul (c i)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp_rw [hinner]
  rw [integral_finsetSum _ fun i _ => (hout i).const_mul (c i)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

theorem integral_integral_archDeriv_eq_zero {Φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ} (hΦc : Continuous Φ)
    (hΦs : WhittakerBlock.IsArchSmooth3 Φ) (i j : Fin 3)
    (hΦ'c : Continuous (WhittakerBlock.archDeriv i j Φ))
    (hcusp : ∀ g, ∫ x, ∫ y, Φ (u x y * g) ∂ν0 ∂ν0 = 0) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∫ x, ∫ y, WhittakerBlock.archDeriv i j Φ (u x y * g) ∂ν0 ∂ν0 = 0 := by
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae

  set F : ℝ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ := fun s x y => Φ (u x y * g * L i j s) with hF
  set F' : ℝ → AdeleRing (𝓞 ℚ) ℚ → AdeleRing (𝓞 ℚ) ℚ → ℂ :=
    fun s x y => ((kap i j s : ℂ)⁻¹) * WhittakerBlock.archDeriv i j Φ (u x y * g * L i j s) with hF'
  have hr : (0 : ℝ) < 1 / 3 := by norm_num
  have hI : ∀ s : closedBall (0 : ℝ) (1 / 3), |(s : ℝ)| < 1 := fun s => by
    have := s.2; have h' : |(s : ℝ)| ≤ 1 / 3 := by simpa [Real.dist_eq] using this
    exact lt_of_le_of_lt h' (by norm_num)
  have hball : ∀ s ∈ ball (0 : ℝ) (1 / 3), |s| < 1 := fun s hs => by
    have h' : |s| < 1 / 3 := by simpa [Real.dist_eq] using hs
    exact lt_trans h' (by norm_num)

  have hLc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => L i j s :=
    continuousOn_iff_continuous_restrict.mp (continuousOn_L i j)
  have huq : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      u q.2.1 q.2.2 * g * L i j q.1 :=
    (((hu.comp (continuous_snd (X := closedBall (0 : ℝ) (1 / 3))) :)).mul continuous_const).mul
      (hLc.comp (continuous_fst (Y := (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :)
  have hFc : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      F q.1 q.2.1 q.2.2 :=
    hΦc.comp huq
  have hkc : Continuous fun s : closedBall (0 : ℝ) (1 / 3) => ((kap i j s : ℂ)⁻¹) := by
    refine Continuous.inv₀ (Complex.continuous_ofReal.comp ((continuous_kap i j).comp continuous_subtype_val))
      fun s => ?_
    exact_mod_cast (kap_pos i j (hI s)).ne'
  have hF'c : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ) =>
      F' q.1 q.2.1 q.2.2 :=
    ((hkc.comp (continuous_fst (Y := (AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ))) :)).mul (hΦ'c.comp huq)

  have hd : ∀ x y, ∀ s ∈ ball (0 : ℝ) (1 / 3), HasDerivAt (fun σ => F σ x y) (F' s x y) s :=
    fun x y s hs => hasDerivAt_comp_L hΦs (u x y * g) i j (hball s hs)

  have hG : ∀ x, ∀ s₀ ∈ ball (0 : ℝ) (1 / 3),
      HasDerivAt (fun s => ∫ y, F s x y ∂ν0) (∫ y, F' s₀ x y ∂ν0) s₀ := fun x =>
    hasDerivAt_integral_of_continuous ν0 hC hνC (fun s y => F s x y) (fun s y => F' s x y) hr
      (hFc.comp (continuous_fst.prodMk ((continuous_const (y := x)).prodMk continuous_snd)) :)
      (hF'c.comp (continuous_fst.prodMk ((continuous_const (y := x)).prodMk continuous_snd)) :) (fun y => hd x y)

  have hGc : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ => ∫ y, F q.1 q.2 y ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ =>
      fun y => F q.1 q.2 y) (hFc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) :)
  have hG'c : Continuous fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ => ∫ y, F' q.1 q.2 y ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : closedBall (0 : ℝ) (1 / 3) × AdeleRing (𝓞 ℚ) ℚ =>
      fun y => F' q.1 q.2 y) (hF'c.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_snd.comp continuous_fst).prodMk continuous_snd)) :)
  have hH : HasDerivAt (fun s => ∫ x, ∫ y, F s x y ∂ν0 ∂ν0) (∫ x, ∫ y, F' 0 x y ∂ν0 ∂ν0) 0 :=
    hasDerivAt_integral_of_continuous ν0 hC hνC (fun s x => ∫ y, F s x y ∂ν0) (fun s x => ∫ y, F' s x y ∂ν0)
      hr hGc hG'c hG 0 (mem_ball_self hr)

  have hzero : (fun s => ∫ x, ∫ y, F s x y ∂ν0 ∂ν0) = fun _ => 0 := by
    funext s
    have := hcusp (g * L i j s)
    simp only [hF, mul_assoc] at this ⊢
    exact this
  rw [hzero] at hH
  have h0 : (∫ x, ∫ y, F' 0 x y ∂ν0 ∂ν0) = 0 := hH.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ)) ▸ rfl
  have hF'0 : ∀ x y, F' 0 x y = WhittakerBlock.archDeriv i j Φ (u x y * g) := fun x y => by
    simp only [hF', L_zero, mul_one, kap, ite_self, add_zero]
    simp
  simp_rw [hF'0] at h0
  exact h0

end Cusp

section Words

theorem isArchSmooth3_sum_translate (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hsa : WhittakerBlock.IsArchSmooth3 f)
    (n : ℕ) (c : Fin n → ℂ) (t : Fin n → AdelicGL 3 (𝓞 ℚ) ℚ) (ht : ∀ i, archComponent3 (𝓞 ℚ) ℚ (t i) = 1) :
    WhittakerBlock.IsArchSmooth3 (fun x => ∑ i, c i * f (x * t i)) := by
  intro g
  have heq : (fun e : Fin 3 → Fin 3 → ℝ => ∑ i, c i * f (g * WhittakerBlock.archRealLift3 e * t i)) =
      fun e => ∑ i, c i * f (g * t i * WhittakerBlock.archRealLift3 e) := by
    funext e
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcomm : t i * WhittakerBlock.archRealLift3 e = WhittakerBlock.archRealLift3 e * t i :=
      commute_archRealLift3 (t i) (ht i) (Matrix.of e)
    rw [mul_assoc, ← hcomm, ← mul_assoc]
  rw [heq]
  exact ContDiffOn.sum fun i _ => contDiffOn_const.mul (hsa (g * t i))

theorem isArchSmooth3_foldr (v : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hv : WhittakerBlock.IsArchSmooth3 v)
    (w : List (Fin 3 × Fin 3)) :
    WhittakerBlock.IsArchSmooth3 (List.foldr (fun ij φ => WhittakerBlock.archDeriv ij.1 ij.2 φ) v w) := by
  induction w with
  | nil => exact hv
  | cons ij w ih => exact isArchSmooth3_archDeriv ih ij.1 ij.2

end Words

section Radicals

theorem continuous_radicalP21 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_apply, radicalP21_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((radicalP21 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -0, 0 * p.2 - p.1; 0, 1, -p.2; 0, 0, 1] := by
      funext p; rfl
    rw [this]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

theorem continuous_radicalP12 :
    Continuous fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ => (radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Function.comp_apply, radicalP12_coe]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  · have : (fun p : AdeleRing (𝓞 ℚ) ℚ × AdeleRing (𝓞 ℚ) ℚ =>
        (((radicalP12 ![p.1, p.2] : AdelicGL 3 (𝓞 ℚ) ℚ)⁻¹ : AdelicGL 3 (𝓞 ℚ) ℚ) :
          Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ))) =
        fun p => !![1, -p.1, p.1 * 0 - p.2; 0, 1, -0; 0, 0, 1] := by
      funext p; rfl
    rw [this]
    refine continuous_pi fun a => continuous_pi fun b => ?_
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop

end Radicals

end R1CuspDeriv
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv"

section WSCBody

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory Filter Topology
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μG" => NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ

theorem WSC.integrable_prod {C : Set 𝔸} (hC : IsCompact C) (hνC : ∀ᵐ y ∂ν0, y ∈ C)
    {K : Set GA} (hK : IsCompact K) (f : 𝔸 → GA → ℂ)
    (hf : Continuous (Function.uncurry f)) (hfK : ∀ x h, h ∉ K → f x h = 0) :
    Integrable (Function.uncurry f) (ν0.prod μG) := by
  haveI : SecondCountableTopology GA := LanglandsTunnell.CubicInduction.adelicGL_secondCountableTopology
  obtain ⟨M, hM⟩ := (hC.prod hK).exists_bound_of_continuousOn hf.continuousOn
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  have hg : Integrable (fun p : 𝔸 × GA => (Set.univ ×ˢ K).indicator (fun _ => (max M 0 : ℝ)) p) (ν0.prod μG) := by
    refine (integrable_indicator_iff (MeasurableSet.univ.prod hKm)).2 (integrableOn_const ?_)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) hK.measure_lt_top.ne
  refine Integrable.mono' hg hf.aestronglyMeasurable ?_
  have hae : ∀ᵐ p ∂ν0.prod μG, p.1 ∈ C :=
    (Measure.quasiMeasurePreserving_fst (μ := ν0) (ν := μG)).ae hνC
  refine hae.mono fun p hp => ?_
  by_cases hpK : p.2 ∈ K
  · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, hpK⟩)]
    exact (hM p ⟨hp, hpK⟩).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem (fun h => hpK (Set.mem_prod.1 h).2)]
    simp [Function.uncurry, hfK p.1 p.2 hpK]

namespace WSC
private theorem _root_.WSC.main
    (ψ : AddChar 𝔸 ℂ) (hψ : Continuous ψ) (u : GA → ℂ) (hu : Continuous u)
    (φ : GA → ℂ) (hφ : IsSmoothingKernel φ) (g : GA) :
    whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) ψ (smoothingOperator φ u) g =
      ∫ h, φ h * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) ψ u (g * h) ∂μG := by
  haveI : SecondCountableTopology GA := LanglandsTunnell.CubicInduction.adelicGL_secondCountableTopology
  obtain ⟨hφc, hφs⟩ := LanglandsTunnell.CubicInduction.continuous_and_hasCompactSupport_of_isSmoothingKernel hφ
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae
  set K : Set GA := tsupport φ with hKdef
  have hK : IsCompact K := hφs
  have hφK : ∀ h, h ∉ K → φ h = 0 := fun h hh => image_eq_zero_of_notMem_tsupport hh

  set F : 𝔸 → 𝔸 → 𝔸 → GA → ℂ := fun x y z h => φ h * (u (upperUnipotent3 x y z * (g * h)) * ψ (-(x + y))) with hF
  have hFc : Continuous fun q : 𝔸 × 𝔸 × 𝔸 × GA => F q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    simp only [hF]
    refine (hφc.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).mul
      ((hu.comp ?_).mul (hψ.comp (continuous_fst.add (continuous_fst.comp continuous_snd)).neg))
    exact (LanglandsTunnell.CubicInduction.continuous_upperUnipotent3.comp
      (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd))))).mul
      (continuous_const.mul (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have hFK : ∀ x y z h, h ∉ K → F x y z h = 0 := fun x y z h hh => by simp only [hF, hφK h hh, zero_mul]

  have hS1 : ∀ x y : 𝔸, ∫ z, ∫ h, F x y z h ∂μG ∂ν0 = ∫ h, ∫ z, F x y z h ∂ν0 ∂μG := by
    intro x y
    exact integral_integral_swap (WSC.integrable_prod hC hνC hK (fun z h => F x y z h)
      (hFc.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))) (fun z h hh => hFK x y z h hh))

  have hG1c : Continuous fun q : 𝔸 × 𝔸 × GA => ∫ z, F q.1 q.2.1 z q.2.2 ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : 𝔸 × 𝔸 × GA => fun z => F q.1 q.2.1 z q.2.2)
      (hFc.comp ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_fst.comp (continuous_snd.comp continuous_fst)).prodMk
          (continuous_snd.prodMk (continuous_snd.comp (continuous_snd.comp continuous_fst))))))

  have hS2 : ∀ x : 𝔸, ∫ y, ∫ h, ∫ z, F x y z h ∂ν0 ∂μG ∂ν0 = ∫ h, ∫ y, ∫ z, F x y z h ∂ν0 ∂ν0 ∂μG := by
    intro x
    exact integral_integral_swap (WSC.integrable_prod hC hνC hK (fun y h => ∫ z, F x y z h ∂ν0)
      (hG1c.comp (continuous_const.prodMk continuous_id))
      (fun y h hh => by simp only [hFK x y _ h hh, integral_zero]))

  have hG2c : Continuous fun q : 𝔸 × GA => ∫ y, ∫ z, F q.1 y z q.2 ∂ν0 ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : 𝔸 × GA => fun y => ∫ z, F q.1 y z q.2 ∂ν0)
      (hG1c.comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst))))

  have hS3 : ∫ x, ∫ h, ∫ y, ∫ z, F x y z h ∂ν0 ∂ν0 ∂μG ∂ν0 = ∫ h, ∫ x, ∫ y, ∫ z, F x y z h ∂ν0 ∂ν0 ∂ν0 ∂μG :=
    integral_integral_swap (WSC.integrable_prod hC hνC hK (fun x h => ∫ y, ∫ z, F x y z h ∂ν0 ∂ν0) hG2c
      (fun x h hh => by simp only [hFK x _ _ h hh, integral_zero]))

  have hL : whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) ψ
      (smoothingOperator φ u) g = ∫ x, ∫ y, ∫ z, ∫ h, F x y z h ∂μG ∂ν0 ∂ν0 ∂ν0 := by
    show ∫ x, ∫ y, ∫ z, smoothingOperator φ u (upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂ν0 ∂ν0 ∂ν0 = _
    simp only [smoothingOperator_apply, hF, ← integral_mul_const, mul_assoc]
  have hR : ∫ h, φ h * whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) ψ u
      (g * h) ∂μG = ∫ h, ∫ x, ∫ y, ∫ z, F x y z h ∂ν0 ∂ν0 ∂ν0 ∂μG := by
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    show φ h * ∫ x, ∫ y, ∫ z, u (upperUnipotent3 x y z * (g * h)) * ψ (-(x + y)) ∂ν0 ∂ν0 ∂ν0 = _
    simp only [hF, ← integral_const_mul]
  rw [hL, hR, ← hS3]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ∫ y, ∫ z, ∫ h, F x y z h ∂μG ∂ν0 ∂ν0 = ∫ h, ∫ y, ∫ z, F x y z h ∂ν0 ∂ν0 ∂μG
  rw [← hS2 x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact hS1 x y

end WSC
p2m_export "" "WSC.main"
end WSCBody
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv"

section EXPINTBody

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory Filter Topology
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2 P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

local notation "GA" => AdelicGL 3 (𝓞 ℚ) ℚ
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "μG" => NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
local notation "pinsQ" => productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)

theorem EXPINT.whittaker3_eq (ψ : AddChar 𝔸 ℂ) (u : GA → ℂ) (g : GA) :
    whittaker3 pinsQ ψ u g = ∫ x, ∫ y, ∫ z, u (upperUnipotent3 x y z * g) * ψ (-(x + y)) ∂ν0 ∂ν0 ∂ν0 := rfl

theorem EXPINT.continuous_whittaker3 (ψ : AddChar 𝔸 ℂ) (hψ : Continuous ψ) (u : GA → ℂ) (hu : Continuous u) :
    Continuous fun g : GA => whittaker3 pinsQ ψ u g := by
  haveI : SecondCountableTopology GA := LanglandsTunnell.CubicInduction.adelicGL_secondCountableTopology
  obtain ⟨C, hC, hνC⟩ := exists_compact_ae
  set F : 𝔸 → 𝔸 → 𝔸 → GA → ℂ := fun x y z g => u (upperUnipotent3 x y z * g) * ψ (-(x + y)) with hF
  have hFc : Continuous fun q : 𝔸 × 𝔸 × 𝔸 × GA => F q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    simp only [hF]
    refine (hu.comp ?_).mul (hψ.comp (continuous_fst.add (continuous_fst.comp continuous_snd)).neg)
    exact (LanglandsTunnell.CubicInduction.continuous_upperUnipotent3.comp
      (continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_snd))))).mul
      (continuous_snd.comp (continuous_snd.comp continuous_snd))

  have hM1 : Continuous fun q : (𝔸 × 𝔸 × GA) × 𝔸 => ((q.1.1, q.1.2.1, q.2, q.1.2.2) : 𝔸 × 𝔸 × 𝔸 × GA) := by
    fun_prop
  have hm1 : Continuous fun q : (𝔸 × 𝔸 × GA) × 𝔸 => F q.1.1 q.1.2.1 q.2 q.1.2.2 := by
    have h := hFc.comp hM1
    simpa only [Function.comp_def] using h
  have hG1c : Continuous fun q : 𝔸 × 𝔸 × GA => ∫ z, F q.1 q.2.1 z q.2.2 ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : 𝔸 × 𝔸 × GA => fun z => F q.1 q.2.1 z q.2.2) hm1

  have hM2 : Continuous fun q : (𝔸 × GA) × 𝔸 => ((q.1.1, q.2, q.1.2) : 𝔸 × 𝔸 × GA) := by fun_prop
  have hm2 : Continuous fun q : (𝔸 × GA) × 𝔸 => ∫ z, F q.1.1 q.2 z q.1.2 ∂ν0 := by
    have h := hG1c.comp hM2
    simpa only [Function.comp_def] using h
  have hG2c : Continuous fun q : 𝔸 × GA => ∫ y, ∫ z, F q.1 y z q.2 ∂ν0 ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun q : 𝔸 × GA => fun y => ∫ z, F q.1 y z q.2 ∂ν0) hm2

  have hM3 : Continuous fun q : GA × 𝔸 => ((q.2, q.1) : 𝔸 × GA) := by fun_prop
  have hm3 : Continuous fun q : GA × 𝔸 => ∫ y, ∫ z, F q.2 y z q.1 ∂ν0 ∂ν0 := by
    have h := hG2c.comp hM3
    simpa only [Function.comp_def] using h
  have hG3c : Continuous fun g : GA => ∫ x, ∫ y, ∫ z, F x y z g ∂ν0 ∂ν0 ∂ν0 :=
    continuous_integral_of_continuous ν0 hC hνC (fun g : GA => fun x => ∫ y, ∫ z, F x y z g ∂ν0 ∂ν0) hm3
  have hfun : (fun g : GA => whittaker3 pinsQ ψ u g) = fun g => ∫ x, ∫ y, ∫ z, F x y z g ∂ν0 ∂ν0 ∂ν0 :=
    funext fun g => EXPINT.whittaker3_eq ψ u g
  rw [hfun]
  exact hG3c

namespace EXPINT

private theorem _root_.EXPINT.main
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : Continuous u)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (m J : ℕ) (e : Fin m → ℂ) (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) :
    (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
        ∫ h, φ h * a i j p.1 (p.2 * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) {p | 0 < p.1}) ∧
    ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (smoothingOperator φ u)
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, (fun i j y₂ k => ∫ h, φ h * a i j y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ := by
  haveI : SecondCountableTopology GA := LanglandsTunnell.CubicInduction.adelicGL_secondCountableTopology
  obtain ⟨hφc, hφs⟩ := LanglandsTunnell.CubicInduction.continuous_and_hasCompactSupport_of_isSmoothingKernel hφ
  have hφK : ∀ h, h ∉ tsupport φ → φ h = 0 := fun h hh => image_eq_zero_of_notMem_tsupport hh
  refine ⟨fun i j => ?_, fun K hK b hb => ?_⟩
  ·
    refine continuousOn_integral_of_compact_support (μ := μG)
      (f := fun (p : ℝ × GA) (h : GA) => φ h * a i j p.1 (p.2 * h)) (k := tsupport φ) hφs ?_ ?_
    · have h1 : Continuous fun q : (ℝ × GA) × GA => φ q.2 := hφc.comp continuous_snd
      have hmap : Continuous fun q : (ℝ × GA) × GA => ((q.1.1, q.1.2 * q.2) : ℝ × GA) :=
        (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).mul continuous_snd)
      have h2 : ContinuousOn (fun q : (ℝ × GA) × GA => a i j q.1.1 (q.1.2 * q.2))
          ({p : ℝ × GA | 0 < p.1} ×ˢ Set.univ) :=
        (hcont i j).comp hmap.continuousOn (fun q hq => (Set.mem_prod.1 hq).1)
      exact h1.continuousOn.mul h2
    · intro p h _ hh
      simp only [hφK h hh, zero_mul]
  ·
    obtain ⟨C, hC⟩ := hexp ((fun q : GA × GA => q.1 * q.2) '' (K ×ˢ tsupport φ))
      ((hK.prod hφs).image (continuous_fst.mul continuous_snd)) b hb
    refine ⟨(∫ h, ‖φ h‖ ∂μG) * C, fun k hk y₂ hy₂ hy₂' y₁ hy₁ hy₁' => ?_⟩
    have hy₂pos : 0 < y₂ := lt_of_lt_of_le (inv_pos.2 (lt_of_lt_of_le one_pos hb)) hy₂
    set Ly : GA := WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) with hLy
    set W : GA → ℂ := fun g => whittaker3 pinsQ NumberField.StandardAddChar.psiQ u g with hW
    have hWc : Continuous W :=
      EXPINT.continuous_whittaker3 _ NumberField.StandardAddChar.continuous_psiQ u hu

    have hac : ∀ i j, Continuous fun h : GA => a i j y₂ (k * h) := fun i j =>
      (hcont i j).comp_continuous (f := fun h : GA => ((y₂, k * h) : ℝ × GA))
        (continuous_const.prodMk (continuous_const.mul continuous_id)) (fun h => hy₂pos)
    have hSc : Continuous fun h : GA => ∑ i : Fin m, ∑ j : Fin J,
        a i j y₂ (k * h) * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) :=
      continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (hac i j).mul continuous_const

    have hφi : Integrable (fun h => ‖φ h‖) μG := (hφc.integrable_of_hasCompactSupport hφs).norm
    have hI1 : Integrable (fun h => φ h * W (Ly * k * h)) μG :=
      (hφc.mul (hWc.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
        (hφs.mul_right (f' := fun h => W (Ly * k * h)))
    have hI2 : ∀ i j, Integrable (fun h => φ h * (a i j y₂ (k * h) *
        ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))) μG := fun i j =>
      (hφc.mul ((hac i j).mul continuous_const)).integrable_of_hasCompactSupport
        (hφs.mul_right (f' := fun h => a i j y₂ (k * h) * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))))
    have hI3 : ∀ i, Integrable (fun h => ∑ j : Fin J, φ h * (a i j y₂ (k * h) *
        ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))) μG := fun i =>
      integrable_finset_sum _ fun j _ => hI2 i j
    have hI4 : Integrable (fun h => φ h * ∑ i : Fin m, ∑ j : Fin J,
        a i j y₂ (k * h) * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))) μG :=
      (hφc.mul hSc).integrable_of_hasCompactSupport (hφs.mul_right (f' := fun h => ∑ i : Fin m, ∑ j : Fin J,
        a i j y₂ (k * h) * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))))

    have h1 : whittaker3 pinsQ NumberField.StandardAddChar.psiQ (smoothingOperator φ u) (Ly * k) =
        ∫ h, φ h * W (Ly * k * h) ∂μG :=
      WSC.main _ NumberField.StandardAddChar.continuous_psiQ u hu φ hφ (Ly * k)

    have h2 : ∫ h, φ h * ∑ i : Fin m, ∑ j : Fin J,
          a i j y₂ (k * h) * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) ∂μG =
        ∑ i : Fin m, ∑ j : Fin J, (∫ h, φ h * a i j y₂ (k * h) ∂μG) *
          ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) := by
      simp_rw [Finset.mul_sum]
      rw [integral_finset_sum _ (fun i _ => hI3 i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ (fun j _ => hI2 i j)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      exact (mul_assoc _ _ _).symm

    rw [h1]
    show ‖(∫ h, φ h * W (Ly * k * h) ∂μG) - ∑ i : Fin m, ∑ j : Fin J, (∫ h, φ h * a i j y₂ (k * h) ∂μG) *
        ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ (∫ h, ‖φ h‖ ∂μG) * C * y₁ ^ τ
    rw [← h2, ← integral_sub hI1 hI4]
    refine (norm_integral_le_of_norm_le (hφi.mul_const (C * y₁ ^ τ)) (Eventually.of_forall fun h => ?_)).trans
      (le_of_eq ?_)
    · rw [← mul_sub, norm_mul]
      by_cases hh : h ∈ tsupport φ
      · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have := hC (k * h) ⟨(k, h), Set.mk_mem_prod hk hh, rfl⟩ y₂ hy₂ hy₂' y₁ hy₁ hy₁'
        simpa only [hW, mul_assoc] using this
      · simp only [hφK h hh, norm_zero, zero_mul, le_refl]
    · rw [integral_mul_const, mul_assoc]

end EXPINT
p2m_export "" "EXPINT.main"
end EXPINTBody
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.R1CuspDeriv"

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hu : Continuous u)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ)
    (m J : ℕ) (e : Fin m → ℂ) (a : Fin m → Fin J → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ => a i j p.1 p.2) {p | 0 < p.1})
    (τ : ℝ)
    (hexp : ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ u
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, a i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ) :
    (∀ i j, ContinuousOn (fun p : ℝ × AdelicGL 3 (𝓞 ℚ) ℚ =>
        ∫ h, φ h * a i j p.1 (p.2 * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) {p | 0 < p.1}) ∧
    ∀ K : Set (AdelicGL 3 (𝓞 ℚ) ℚ), IsCompact K → ∀ b : ℝ, 1 ≤ b → ∃ C : ℝ, ∀ k ∈ K,
          ∀ y₂ : ℝ, b⁻¹ ≤ y₂ → y₂ ≤ b → ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 →
          ‖whittaker3 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ))
              NumberField.StandardAddChar.psiQ (smoothingOperator φ u)
              (WhittakerBlock.archRealLift3 (fun i j => if i = j then ![y₁ * y₂, y₂, 1] i else 0) * k) -
            (∑ i : Fin m, ∑ j : Fin J, (fun i j y₂ k => ∫ h, φ h * a i j y₂ (k * h) ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ)) i j y₂ k * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)))‖ ≤
          C * y₁ ^ τ :=
  EXPINT.main u hu φ hφ m J e a hcont τ hexp

end S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_exists_expansion_whittaker3_smoothingOperator (solution)
