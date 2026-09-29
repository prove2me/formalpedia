-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.SlabL2.hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/1d95fc68-fb8f-5f08-9819-dcc0fdbe9817

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Basic
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_archDeriv_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_continuous_and_isArchSmooth3_smoothingOperator
import Theorems.Thm_LanglandsTunnell_CubicInduction_ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3
import Theorems.Thm_LanglandsTunnell_CubicInduction_WhittakerBlock_archRealLift3_one_and_ideleNorm_det_archRealLift3
import Theorems.Thm_LanglandsTunnell_CubicInduction_SlabL2_isFiniteMeasure_domainMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions WhittakerBlock.sigmaCompactSpace_adelicGL3 M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.CubicInduction.WhittakerBlock.coe_archDerivₗ_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff AutomorphicForm.HeckeEigensystem.ofRawCentral_toRawCentral AutomorphicForm.HeckeEigensystem.toRawCentral_ofRawCentral AutomorphicForm.HeckeEigensystem.ofRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_b AutomorphicForm.HeckeEigensystem.toRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_a AutomorphicForm.HeckeEigensystem.ofRawCentral_level AutomorphicForm.HeckeEigensystem.toRawCentral_b AutomorphicForm.SmoothCuspRealizationAt.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.degenerateEigensystem_a AutomorphicForm.SmoothCuspRealizationAt.mk.sizeOf_spec AutomorphicForm.degenerateEigensystem_b AutomorphicForm.HeckeEigensystem.map_b AutomorphicForm.HeckeEigensystem.map_a AutomorphicForm.HeckeEigensystem.map_level IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul LanglandsTunnell.CubicInduction.diagonal3_coe LanglandsTunnell.CubicInduction.halfModulus3_one LanglandsTunnell.CubicInduction.torusChar3_one LanglandsTunnell.CubicInduction.fnTwist3_apply"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField AutomorphicForm MeasureTheory
open LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace PDerivGlue

scoped instance : LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
scoped instance : T2Space (Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → AdeleRing (𝓞 ℚ) ℚ))
scoped instance : LocallyCompactSpace (AdelicGL 3 (𝓞 ℚ) ℚ) := inferInstance

abbrev eArr (i j : Fin 3) (s : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun a c => (if a = c then (1 : ℝ) else 0) + if a = i ∧ c = j then s else 0

abbrev L (i j : Fin 3) (s : ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ := WhittakerBlock.archRealLift3 (eArr i j s)

abbrev dlt (i j : Fin 3) (s : ℝ) : ℝ := 1 + if i = j then s else 0

theorem det_eArr (i j : Fin 3) (s : ℝ) : (Matrix.of (eArr i j s)).det = dlt i j s := by
  fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_three, eArr, dlt]

theorem eArr_zero (i j : Fin 3) : eArr i j 0 = fun a c : Fin 3 => if a = c then (1 : ℝ) else 0 := by
  funext a c; simp [eArr]

theorem L_zero (i j : Fin 3) : L i j 0 = 1 := by
  show WhittakerBlock.archRealLift3 (eArr i j 0) = 1
  rw [eArr_zero]
  exact LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3.1

theorem dlt_zero (i j : Fin 3) : dlt i j 0 = 1 := by simp [dlt]

theorem dlt_mem {i j : Fin 3} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) :
    1 / 2 ≤ dlt i j s ∧ dlt i j s ≤ 2 := by
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt] at hs
  unfold dlt
  split_ifs <;> constructor <;> linarith

theorem dlt_pos {i j : Fin 3} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) : 0 < dlt i j s := by
  have := (dlt_mem (i := i) (j := j) hs).1; linarith

theorem dlt_ne_zero {i j : Fin 3} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) :
    1 + (if i = j then s else 0) ≠ 0 := (dlt_pos hs).ne'

theorem norm_inv_dlt_le {i j : Fin 3} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) :
    ‖(((dlt i j s)⁻¹ : ℝ) : ℂ)‖ ≤ 2 := by
  obtain ⟨h1, _⟩ := dlt_mem (i := i) (j := j) hs
  have hp : 0 < dlt i j s := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp)]
  calc (dlt i j s)⁻¹ ≤ (1 / 2)⁻¹ := by
        exact inv_anti₀ (by norm_num) h1
    _ = 2 := by norm_num

theorem ideleNorm_det_L {i j : Fin 3} {s : ℝ} (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (L i j s)) = dlt i j s := by
  have h := LanglandsTunnell.CubicInduction.WhittakerBlock.archRealLift3_one_and_ideleNorm_det_archRealLift3.2
    (eArr i j s) (by rw [det_eArr]; exact dlt_pos hs)
  rw [det_eArr] at h
  exact h

theorem mem_slab_mul_L {a b : ℝ} (ha : 0 < a) (hab : a < b) {i j : Fin 3} {s : ℝ}
    (hs : s ∈ Metric.ball (0 : ℝ) (1 / 2)) {g : AdelicGL 3 (𝓞 ℚ) ℚ}
    (hg : NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b) :
    NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g * L i j s)) ∈ Set.Icc (a / 2) (2 * b) := by
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul, ideleNorm_det_L hs]
  obtain ⟨h1, h2⟩ := dlt_mem (i := i) (j := j) hs
  obtain ⟨hg1, hg2⟩ := hg
  have hb : 0 < b := ha.trans hab
  have hn : 0 ≤ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := ha.le.trans hg1
  constructor <;> nlinarith

end PDerivGlue
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj.PDerivGlue"

open PDerivGlue in
theorem solution
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hω : ∀ z : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖(ω z : ℂ)‖ = 1)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (hW0a :
      ∃ c C : ℝ, 0 < c ∧ ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
        ∃ (γ : GL (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
          globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧
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
                (archPlaceComponent3 ℚ w k : Matrix (Fin 3) (Fin 3) w.Completion) = 1)
    (u : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hc : Continuous u)
    (haut : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = u g)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * u g)
    (hmg : IsModerateGrowth3 ℚ u)
    (hP21 : IsCuspidalAlongP21 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (hP12 : IsCuspidalAlongP12 (productionPinsOf ℚ ∅ (fun _ => ⊥) (fun _ => 1) (AdelicBox.adelicBox ℚ)) u)
    (φ φ' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ : IsSmoothingKernel φ) (hφ' : IsSmoothingKernel φ')
    (i j : Fin 3) :
    HasDerivAt
      (fun s : ℝ => ∫ g, smoothingOperator φ u
          (g * WhittakerBlock.archRealLift3 (fun a c => (if a = c then (1 : ℝ) else 0) + if a = i ∧ c = j then s else 0)) *
        (starRingEnd ℂ) (smoothingOperator φ' u
          (g * WhittakerBlock.archRealLift3 (fun a c => (if a = c then (1 : ℝ) else 0) + if a = i ∧ c = j then s else 0)))
        ∂(domainMeasure a b Φ₀))
      ((∫ g, WhittakerBlock.archDeriv i j (smoothingOperator φ u) g * (starRingEnd ℂ) (smoothingOperator φ' u g)
          ∂(domainMeasure a b Φ₀)) +
        ∫ g, smoothingOperator φ u g * (starRingEnd ℂ) (WhittakerBlock.archDeriv i j (smoothingOperator φ' u) g)
          ∂(domainMeasure a b Φ₀))
      0 := by
  classical
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ
  haveI : IsFiniteMeasure (domainMeasure a b Φ₀) := isFiniteMeasure_domainMeasure a b Φ₀ hΦ₀
  have ha : 0 < a := hΦ₀.pos
  have hab : a < b := hΦ₀.lt
  have ha2 : 0 < a / 2 := by positivity
  have hab2 : a / 2 < 2 * b := by linarith

  set F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := smoothingOperator φ u with hF
  set F' : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := smoothingOperator φ' u with hF'
  have hu : LocallyIntegrable u (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ) := hc.locallyIntegrable
  obtain ⟨hcF, hsF⟩ := continuous_and_isArchSmooth3_smoothingOperator φ u hφ hu
  obtain ⟨hcF', hsF'⟩ := continuous_and_isArchSmooth3_smoothingOperator φ' u hφ' hu
  obtain ⟨hφij, hDF⟩ := archDeriv_smoothingOperator φ u hφ hu i j
  obtain ⟨hφ'ij, hDF'⟩ := archDeriv_smoothingOperator φ' u hφ' hu i j

  set φij : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun y => -deriv (fun s : ℝ => φ (WhittakerBlock.archRealLift3 (fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0 with hφij_def
  set φ'ij : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun y => -deriv (fun s : ℝ => φ' (WhittakerBlock.archRealLift3 (fun a b =>
        (if a = b then (1 : ℝ) else 0) + if a = i ∧ b = j then s else 0) * y)) 0 with hφ'ij_def
  have hcDF : Continuous (WhittakerBlock.archDeriv i j F) := by
    rw [hDF]; exact (continuous_and_isArchSmooth3_smoothingOperator φij u hφij hu).1
  have hcDF' : Continuous (WhittakerBlock.archDeriv i j F') := by
    rw [hDF']; exact (continuous_and_isArchSmooth3_smoothingOperator φ'ij u hφ'ij hu).1

  obtain ⟨B1, hB1⟩ := exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc ω hW0a u hc haut hcen hmg hP21 hP12
    φ hφ (a / 2) (2 * b) ha2 hab2
  obtain ⟨B2, hB2⟩ := exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc ω hW0a u hc haut hcen hmg hP21 hP12
    φ' hφ' (a / 2) (2 * b) ha2 hab2
  obtain ⟨B3, hB3⟩ := exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc ω hW0a u hc haut hcen hmg hP21 hP12
    φij hφij (a / 2) (2 * b) ha2 hab2
  obtain ⟨B4, hB4⟩ := exists_forall_norm_smoothingOperator_le_of_ideleNorm_det_mem_Icc ω hW0a u hc haut hcen hmg hP21 hP12
    φ'ij hφ'ij (a / 2) (2 * b) ha2 hab2
  have hB1' : ∀ g, NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (a / 2) (2 * b) →
      ‖F g‖ ≤ |B1| := fun g hg => (hB1 g hg).trans (le_abs_self _)
  have hB2' : ∀ g, NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (a / 2) (2 * b) →
      ‖F' g‖ ≤ |B2| := fun g hg => (hB2 g hg).trans (le_abs_self _)
  have hB3' : ∀ g, NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (a / 2) (2 * b) →
      ‖WhittakerBlock.archDeriv i j F g‖ ≤ |B3| := fun g hg => by
    rw [hDF]; exact (hB3 g hg).trans (le_abs_self _)
  have hB4' : ∀ g, NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (a / 2) (2 * b) →
      ‖WhittakerBlock.archDeriv i j F' g‖ ≤ |B4| := fun g hg => by
    rw [hDF']; exact (hB4 g hg).trans (le_abs_self _)

  obtain ⟨_, hslab⟩ := ideleNorm_det_globalPointsGL_eq_one_and_measurableSet_ideleNormDetSlab
  have hae : ∀ᵐ g ∂(domainMeasure a b Φ₀),
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := by
    rw [domainMeasure_def, slabMeasure_def]
    exact ae_restrict_of_ae (ae_restrict_mem (hslab a b))

  set Fn : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun s g => F (g * L i j s) * (starRingEnd ℂ) (F' (g * L i j s)) with hFn
  set Fn' : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun s g =>
      ((((dlt i j s)⁻¹ : ℝ) : ℂ) * WhittakerBlock.archDeriv i j F (g * L i j s)) * (starRingEnd ℂ) (F' (g * L i j s)) +
      F (g * L i j s) * (starRingEnd ℂ) ((((dlt i j s)⁻¹ : ℝ) : ℂ) * WhittakerBlock.archDeriv i j F' (g * L i j s))
    with hFn'

  have hmulL : ∀ s : ℝ, Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => g * L i j s := fun s => continuous_id.mul continuous_const
  have hmeasFn : ∀ s, AEStronglyMeasurable (Fn s) (domainMeasure a b Φ₀) := fun s => by
    refine Continuous.aestronglyMeasurable ?_
    exact (hcF.comp (hmulL s)).mul (Complex.continuous_conj.comp (hcF'.comp (hmulL s)))
  have hmeasFn' : ∀ s, AEStronglyMeasurable (Fn' s) (domainMeasure a b Φ₀) := fun s => by
    refine Continuous.aestronglyMeasurable ?_
    exact ((continuous_const.mul (hcDF.comp (hmulL s))).mul
      (Complex.continuous_conj.comp (hcF'.comp (hmulL s)))).add
      ((hcF.comp (hmulL s)).mul
        (Complex.continuous_conj.comp (continuous_const.mul (hcDF'.comp (hmulL s)))))

  set K : ℝ := 2 * |B3| * |B2| + |B1| * (2 * |B4|) with hK
  have hball : Metric.ball (0 : ℝ) (1 / 2) ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds 0 (by norm_num)
  have h0ball : (0 : ℝ) ∈ Metric.ball (0 : ℝ) (1 / 2) := Metric.mem_ball_self (by norm_num)
  have hbound : ∀ᵐ g ∂(domainMeasure a b Φ₀), ∀ s ∈ Metric.ball (0 : ℝ) (1 / 2), ‖Fn' s g‖ ≤ K := by
    filter_upwards [hae] with g hg s hs
    have hgs := mem_slab_mul_L ha hab hs hg (i := i) (j := j)
    have e1 := norm_inv_dlt_le (i := i) (j := j) hs
    have e2 := hB3' _ hgs
    have e3 := hB2' _ hgs
    have e4 := hB1' _ hgs
    have e5 := hB4' _ hgs
    simp only [hFn']
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, norm_mul, Complex.norm_conj]
      gcongr
    · rw [norm_mul, Complex.norm_conj, norm_mul]
      gcongr

  have hdiff : ∀ᵐ g ∂(domainMeasure a b Φ₀), ∀ s ∈ Metric.ball (0 : ℝ) (1 / 2),
      HasDerivAt (fun r => Fn r g) (Fn' s g) s := by
    refine Filter.Eventually.of_forall fun g s hs => ?_
    have h1 : HasDerivAt (fun r : ℝ => F (g * L i j r))
        ((((dlt i j s)⁻¹ : ℝ) : ℂ) * WhittakerBlock.archDeriv i j F (g * L i j s)) s :=
      WhittakerBlock.hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3 F hsF g i j s (dlt_ne_zero hs)
    have h2 : HasDerivAt (fun r : ℝ => F' (g * L i j r))
        ((((dlt i j s)⁻¹ : ℝ) : ℂ) * WhittakerBlock.archDeriv i j F' (g * L i j s)) s :=
      WhittakerBlock.hasDerivAt_apply_mul_archRealLift3_of_isArchSmooth3 F' hsF' g i j s (dlt_ne_zero hs)
    have h2c : HasDerivAt (fun r : ℝ => (starRingEnd ℂ) (F' (g * L i j r)))
        ((starRingEnd ℂ) ((((dlt i j s)⁻¹ : ℝ) : ℂ) * WhittakerBlock.archDeriv i j F' (g * L i j s))) s := by
      have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt s h2
      first | exact this | simpa using this | simpa [Function.comp_def] using this
    simp only [hFn, hFn']
    exact h1.mul h2c

  have hsub : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
      NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (a / 2) (2 * b) :=
    fun g hg => ⟨by linarith [hg.1], by linarith [hg.2, ha.trans hab]⟩
  have hint0 : Integrable (Fn 0) (domainMeasure a b Φ₀) := by
    refine Integrable.of_bound (hmeasFn 0) (|B1| * |B2|) ?_
    filter_upwards [hae] with g hg
    have hgs := mem_slab_mul_L ha hab h0ball hg (i := i) (j := j)
    simp only [hFn]
    rw [norm_mul, Complex.norm_conj]
    have e4 := hB1' _ hgs
    have e3 := hB2' _ hgs
    gcongr

  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hball
    (Filter.Eventually.of_forall hmeasFn) hint0 (hmeasFn' 0) hbound (integrable_const K) hdiff).2

  have hA : Integrable (fun g => WhittakerBlock.archDeriv i j F g * (starRingEnd ℂ) (F' g)) (domainMeasure a b Φ₀) := by
    refine Integrable.of_bound ?_ (|B3| * |B2|) ?_
    · exact (hcDF.mul (Complex.continuous_conj.comp hcF')).aestronglyMeasurable
    · filter_upwards [hae] with g hg
      rw [norm_mul, Complex.norm_conj]
      have e2 := hB3' _ (hsub g hg)
      have e3 := hB2' _ (hsub g hg)
      gcongr
  have hB : Integrable (fun g => F g * (starRingEnd ℂ) (WhittakerBlock.archDeriv i j F' g)) (domainMeasure a b Φ₀) := by
    refine Integrable.of_bound ?_ (|B1| * |B4|) ?_
    · exact (hcF.mul (Complex.continuous_conj.comp hcDF')).aestronglyMeasurable
    · filter_upwards [hae] with g hg
      rw [norm_mul, Complex.norm_conj]
      have e4 := hB1' _ (hsub g hg)
      have e5 := hB4' _ (hsub g hg)
      gcongr
  have h0 : Fn' 0 = fun g => WhittakerBlock.archDeriv i j F g * (starRingEnd ℂ) (F' g) +
      F g * (starRingEnd ℂ) (WhittakerBlock.archDeriv i j F' g) := by
    funext g
    simp only [hFn', L_zero, dlt_zero, mul_one, inv_one, Complex.ofReal_one, one_mul]
  have hval : ∫ g, Fn' 0 g ∂(domainMeasure a b Φ₀) =
      (∫ g, WhittakerBlock.archDeriv i j F g * (starRingEnd ℂ) (F' g) ∂(domainMeasure a b Φ₀)) +
        ∫ g, F g * (starRingEnd ℂ) (WhittakerBlock.archDeriv i j F' g) ∂(domainMeasure a b Φ₀) := by
    rw [h0]
    exact integral_add hA hB
  exact key.congr_deriv hval

end
end S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_hasDerivAt_integral_smoothingOperator_comp_archRealLift3_mul_conj (solution)
