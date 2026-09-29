-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/d246dbd7-0871-561c-ab77-8c46079e80c8

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Theorems.Thm_LanglandsTunnell_CubicInduction_summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val"

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm LanglandsTunnell.Converse

private theorem norm_mul_ofReal_cpow_sub_one {α : Type} (φ : α → ℂ) (N : α → ℝ) (hpos : ∀ a, 0 < N a) (s : ℂ)
    (a : α) : ‖φ a * ((N a : ℝ) : ℂ) ^ (s - 1)‖ = ‖φ a‖ * N a ^ (s.re - 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hpos a), Complex.sub_re, Complex.one_re]

private theorem aestronglyMeasurable_mul_ofReal_cpow_sub_one {α : Type} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} {N : α → ℝ} (hN : Measurable N) (hφ : AEStronglyMeasurable φ μ) (s : ℂ) :
    AEStronglyMeasurable (fun a => φ a * ((N a : ℝ) : ℂ) ^ (s - 1)) μ :=
  hφ.mul ((Complex.measurable_ofReal.comp hN).pow_const (s - 1)).aestronglyMeasurable

private theorem integrableOn_norm_mul_rpow_setOf_one_le {α : Type} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} {N : α → ℝ} (hpos : ∀ a, 0 < N a) (hN : Measurable N) (hφ : AEStronglyMeasurable φ μ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun a => ‖φ a‖ * N a ^ (σ - 1)) μ) (r : ℝ) :
    IntegrableOn (fun a => ‖φ a‖ * N a ^ (r - 1)) {a | 1 ≤ N a} μ := by
  have hset : MeasurableSet {a | 1 ≤ N a} := measurableSet_le measurable_const hN
  refine (hint (max σ₀ r) (le_max_left _ _)).integrableOn.mono' ?_ ?_
  · exact (hφ.norm.mul (hN.pow_const (r - 1)).aestronglyMeasurable).restrict
  · refine (ae_restrict_mem hset).mono fun a ha => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hpos a).le _))]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ha (by linarith [le_max_right σ₀ r])) (norm_nonneg _)

private theorem integrable_mul_ofReal_cpow_sub_one_of_le_re {α : Type} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} {N : α → ℝ} (hpos : ∀ a, 0 < N a) (hN : Measurable N) (hφ : AEStronglyMeasurable φ μ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun a => ‖φ a‖ * N a ^ (σ - 1)) μ) {s : ℂ} (hs : σ₀ ≤ s.re) :
    Integrable (fun a => φ a * ((N a : ℝ) : ℂ) ^ (s - 1)) μ :=
  (hint s.re hs).mono' (aestronglyMeasurable_mul_ofReal_cpow_sub_one hN hφ s)
    (Filter.Eventually.of_forall fun a => (norm_mul_ofReal_cpow_sub_one φ N hpos s a).le)

private theorem norm_setIntegral_mul_ofReal_cpow_sub_one_le {α : Type} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} {N : α → ℝ} (hpos : ∀ a, 0 < N a) (hN : Measurable N) (hφ : AEStronglyMeasurable φ μ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun a => ‖φ a‖ * N a ^ (σ - 1)) μ) (b : ℝ) {s : ℂ} (hs : s.re ≤ b) :
    ‖∫ a in {a | 1 ≤ N a}, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ‖ ≤
      ∫ a in {a | 1 ≤ N a}, ‖φ a‖ * N a ^ (max σ₀ b - 1) ∂μ := by
  have hset : MeasurableSet {a | 1 ≤ N a} := measurableSet_le measurable_const hN
  refine norm_integral_le_of_norm_le (integrableOn_norm_mul_rpow_setOf_one_le hpos hN hφ σ₀ hint _) ?_
  refine (ae_restrict_mem hset).mono fun a ha => ?_
  rw [norm_mul_ofReal_cpow_sub_one φ N hpos s a]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le ha (by linarith [le_max_right σ₀ b])) (norm_nonneg _)

private theorem hasDerivAt_setIntegral_mul_ofReal_cpow_sub_one {α : Type} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℂ} {N : α → ℝ} (hpos : ∀ a, 0 < N a) (hN : Measurable N) (hφ : AEStronglyMeasurable φ μ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun a => ‖φ a‖ * N a ^ (σ - 1)) μ) (s₀ : ℂ) :
    HasDerivAt (fun s : ℂ => ∫ a in {a | 1 ≤ N a}, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ)
      (∫ a in {a | 1 ≤ N a}, φ a * ((N a : ℝ) : ℂ) ^ (s₀ - 1) * Complex.log ((N a : ℝ) : ℂ) ∂μ) s₀ := by
  have hset : MeasurableSet {a | 1 ≤ N a} := measurableSet_le measurable_const hN
  have hlogm : Measurable fun a => Complex.log ((N a : ℝ) : ℂ) :=
    Complex.measurable_log.comp (Complex.measurable_ofReal.comp hN)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict {a | 1 ≤ N a})
    (F := fun s a => φ a * ((N a : ℝ) : ℂ) ^ (s - 1))
    (F' := fun s a => φ a * ((N a : ℝ) : ℂ) ^ (s - 1) * Complex.log ((N a : ℝ) : ℂ))
    (bound := fun a => ‖φ a‖ * N a ^ (max σ₀ (s₀.re + 2) - 1)) (Metric.ball_mem_nhds s₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall fun s =>
      (aestronglyMeasurable_mul_ofReal_cpow_sub_one hN hφ s).restrict
  · have h := integrableOn_norm_mul_rpow_setOf_one_le hpos hN hφ σ₀ hint s₀.re
    exact h.mono' (aestronglyMeasurable_mul_ofReal_cpow_sub_one hN hφ s₀).restrict
      (Filter.Eventually.of_forall fun a => (norm_mul_ofReal_cpow_sub_one φ N hpos s₀ a).le)
  · exact (aestronglyMeasurable_mul_ofReal_cpow_sub_one hN hφ s₀).restrict.mul hlogm.aestronglyMeasurable
  · refine (ae_restrict_mem hset).mono fun a ha s hs => ?_
    have hNa : 0 < N a := hpos a
    have hre : s.re ≤ s₀.re + 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm (s - s₀)
      have h2 : ‖s - s₀‖ < 1 := by simpa [dist_eq_norm] using hs
      have h3 : (s - s₀).re = s.re - s₀.re := Complex.sub_re s s₀
      linarith [le_abs_self (s - s₀).re]
    have hlog : ‖Complex.log ((N a : ℝ) : ℂ)‖ ≤ N a := by
      rw [← Complex.ofReal_log hNa.le, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg ha)]
      linarith [Real.log_le_sub_one_of_pos hNa]
    rw [norm_mul, norm_mul_ofReal_cpow_sub_one φ N hpos s a, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc N a ^ (s.re - 1) * ‖Complex.log ((N a : ℝ) : ℂ)‖
        ≤ N a ^ (s.re - 1) * N a ^ (1 : ℝ) := by
          rw [Real.rpow_one]; exact mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hNa.le _)
      _ = N a ^ (s.re - 1 + 1) := (Real.rpow_add hNa _ _).symm
      _ ≤ N a ^ (max σ₀ (s₀.re + 2) - 1) :=
          Real.rpow_le_rpow_of_exponent_le ha (by linarith [le_max_right σ₀ (s₀.re + 2)])
  · exact integrableOn_norm_mul_rpow_setOf_one_le hpos hN hφ σ₀ hint _
  · refine Filter.Eventually.of_forall fun a s _ => ?_
    have hne : ((N a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos a).ne'
    have h := ((hasDerivAt_id s).sub_const (1 : ℂ)).const_cpow (c := ((N a : ℝ) : ℂ)) (Or.inl hne)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h.const_mul (φ a)

private theorem exists_differentiable_boundedOnStrips_integral_eq_add_of_integrable {α : Type} [MeasurableSpace α]
    (μ : Measure α) (φ : α → ℂ) (N : α → ℝ) (hpos : ∀ a, 0 < N a) (hN : Measurable N)
    (hφ : AEStronglyMeasurable φ μ) (σ₀ : ℝ)
    (hint : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun a => ‖φ a‖ * N a ^ (σ - 1)) μ) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧
      (∀ s : ℂ, E s = ∫ a in {a | 1 ≤ N a}, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ) ∧
      ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
        (∫ a, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ) =
          (∫ a in {a | 1 ≤ N a}, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ) +
            ∫ a in {a | N a < 1}, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  refine ⟨fun s => ∫ a in {a | 1 ≤ N a}, φ a * ((N a : ℝ) : ℂ) ^ (s - 1) ∂μ, ?_, ?_, fun s => rfl, σ₀, ?_⟩
  · exact fun s₀ => (hasDerivAt_setIntegral_mul_ofReal_cpow_sub_one hpos hN hφ σ₀ hint s₀).differentiableAt
  · intro b₁ b₂
    exact ⟨∫ a in {a | 1 ≤ N a}, ‖φ a‖ * N a ^ (max σ₀ b₂ - 1) ∂μ, fun s _ hs =>
      norm_setIntegral_mul_ofReal_cpow_sub_one_le hpos hN hφ σ₀ hint b₂ hs⟩
  · intro s hs
    have hset : MeasurableSet {a | 1 ≤ N a} := measurableSet_le measurable_const hN
    have hcompl : {a | 1 ≤ N a}ᶜ = {a | N a < 1} :=
      Set.ext fun a => by simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [← hcompl]
    exact (integral_add_compl hset (integrable_mul_ofReal_cpow_sub_one_of_le_re hpos hN hφ σ₀ hint hs.le)).symm

private theorem integrable_norm_mul_mul_rpow_of_norm_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α}
    {W χ : α → ℂ} {N : α → ℝ} (hχ : ∀ a, ‖χ a‖ = 1) {σ : ℝ}
    (h : Integrable (fun a => ‖W a‖ * N a ^ (σ - 1)) μ) :
    Integrable (fun a => ‖W a * χ a‖ * N a ^ (σ - 1)) μ := by
  refine h.congr (Filter.Eventually.of_forall fun a => ?_)
  simp only [norm_mul, hχ a, mul_one]

private theorem coe_iotaGL_diagUnitGL2_eq {A : Type*} [CommRing A] (a : Aˣ) :
    ((LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) :
        Matrix.GeneralLinearGroup (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) =
      !![(a : A), 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem coe_inv_iotaGL_diagUnitGL2_eq {A : Type*} [CommRing A] (a : Aˣ) :
    (((LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) :
        Matrix.GeneralLinearGroup (Fin 3) A)⁻¹ : Matrix.GeneralLinearGroup (Fin 3) A) :
          Matrix (Fin 3) (Fin 3) A) =
      !![((a⁻¹ : Aˣ) : A), 0, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem continuous_iotaGL_diagUnitGL2 {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :
    Continuous fun a : Aˣ =>
      (LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) :
        Matrix.GeneralLinearGroup (Fin 3) A) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · simp only [Function.comp_def, coe_iotaGL_diagUnitGL2_eq]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
    all_goals first
      | exact continuous_const | exact Units.continuous_val
  · simp only [coe_inv_iotaGL_diagUnitGL2_eq]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
    all_goals first
      | exact continuous_const | exact Units.continuous_val | exact Units.continuous_coe_inv

private theorem continuous_iotaGL_diagUnitGL2_adele :
    Continuous fun a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ =>
      LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) :=
  continuous_iotaGL_diagUnitGL2

private theorem continuous_iotaGL_diagUnitGL2_mul
    (g : LanglandsTunnell.CubicInduction.AdelicGL 3 (NumberField.RingOfIntegers ℚ) ℚ) :
    Continuous fun a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ =>
      LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) * g :=
  continuous_iotaGL_diagUnitGL2_adele.mul continuous_const

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel in
open LanglandsTunnell LanglandsTunnell.CubicInduction in
theorem solution
    (W : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hWc : Continuous W) (hW : IsGaugeMajorised3 ℚ W)
    (χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (hχadm : IsAdmissibleTwist ℚ χ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∃ E : ℂ → ℂ, Differentiable ℂ E ∧ LanglandsTunnell.LDatum.BoundedOnStrips E ∧
      (∀ s : ℂ, E s =
        ∫ a in {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | 1 ≤ TateGlobal.ideleNorm ℚ a},
          W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
            ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
          ∂(NumberField.Idele.idelicHaar ℚ)) ∧
      ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
        globalZeta30 W χ s g =
          E s +
            ∫ a in {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | TateGlobal.ideleNorm ℚ a < 1},
              W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
                ((TateGlobal.ideleNorm ℚ a : ℝ) : ℂ) ^ (s - 1)
              ∂(NumberField.Idele.idelicHaar ℚ) := by
  obtain ⟨σ₀, hint⟩ :=
    (LanglandsTunnell.CubicInduction.summable_growth_continuous_halfPlane_integrable_of_isGaugeMajorised3 W hWc
      hW).2.2.2.2.1 g
  obtain ⟨-, hχcont, hχu⟩ := hχadm
  have hu : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ‖((χ a : ℂˣ) : ℂ)‖ = 1 := hχu
  have hχc : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ((χ a : ℂˣ) : ℂ) := Units.continuous_val.comp hχcont
  have hφ : AEStronglyMeasurable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      W (LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) * g) *
        ((χ a : ℂˣ) : ℂ)) (NumberField.Idele.idelicHaar ℚ) :=
    ((hWc.comp (continuous_iotaGL_diagUnitGL2_mul g)).mul hχc).aestronglyMeasurable
  have hN : Measurable (NumberField.TateGlobal.ideleNorm ℚ) :=
    (NumberField.TateGlobal.continuous_ideleNorm ℚ).measurable
  have hint' : ∀ σ : ℝ, σ₀ ≤ σ → Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
      ‖W (LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) * g) *
          ((χ a : ℂˣ) : ℂ)‖ * NumberField.TateGlobal.ideleNorm ℚ a ^ (σ - 1)) (NumberField.Idele.idelicHaar ℚ) :=
    fun σ hσ => integrable_norm_mul_mul_rpow_of_norm_eq_one hu (hint σ hσ)
  obtain ⟨E, hE, hB, hEq, σ₁, hsplit⟩ :=
    exists_differentiable_boundedOnStrips_integral_eq_add_of_integrable (NumberField.Idele.idelicHaar ℚ)
      (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ =>
        W (LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 a) * g) *
          ((χ a : ℂˣ) : ℂ))
      (NumberField.TateGlobal.ideleNorm ℚ) NumberField.TateGlobal.ideleNorm_pos hN hφ σ₀ hint'
  refine ⟨E, hE, hB, hEq, σ₁, fun s hs => ?_⟩
  rw [LanglandsTunnell.CubicInduction.globalZeta30, hEq s]
  exact hsplit s hs

end S_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_differentiable_boundedOnStrips_globalZeta30_eq_add_of_integrable (solution)
