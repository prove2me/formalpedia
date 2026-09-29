-- Prove2me | solution 1 for NumberField.AdicCompletion.map_matrix_mulVec_pi_eq_smul_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/21b66b11-6a1b-55ea-a4a5-cd9e4f96f0fa

import Mathlib
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Matrix Set
open scoped ENNReal NNReal Pointwise

namespace KcAdicLinCV

variable {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]

local notation "F" => v.adicCompletion K

theorem measure_smul_set (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0) (s : Set F) :
    μ (a • s) = (‖a‖₊ : ℝ≥0∞) * μ s := by
  have h := MeasureTheory.distribHaarChar_mul μ (Units.mk0 a ha) s
  have hmod : distribHaarChar F (Units.mk0 a ha) = ‖a‖₊ := by
    rw [← LanglandsTunnell.TateLocal.modulus_of_ne_zero ha]
    exact LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm K v a
  rw [hmod] at h
  exact h.symm

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in

theorem preimage_mul_left_eq (a : F) (ha : a ≠ 0) (s : Set F) :
    (fun x => a * x) ⁻¹' s = a⁻¹ • s := by
  ext x
  rw [Set.mem_preimage, Set.mem_inv_smul_set_iff₀ ha, smul_eq_mul]

theorem measure_preimage_mul_left (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0)
    (s : Set F) : μ ((fun x => a * x) ⁻¹' s) = (‖a‖₊ : ℝ≥0∞)⁻¹ * μ s := by
  rw [preimage_mul_left_eq a ha, measure_smul_set μ a⁻¹ (inv_ne_zero ha), nnnorm_inv,
    ENNReal.coe_inv (nnnorm_ne_zero_iff.2 ha)]

theorem map_mul_left (μ : Measure F) [μ.IsAddHaarMeasure] (a : F) (ha : a ≠ 0) :
    Measure.map (fun x => a * x) μ = (‖a‖₊ : ℝ≥0∞)⁻¹ • μ := by
  ext s hs
  rw [Measure.map_apply (measurable_const_mul a) hs, Measure.smul_apply, smul_eq_mul,
    measure_preimage_mul_left μ a ha]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem measurable_mulVec (M : Matrix ι ι F) : Measurable fun x : ι → F => M.mulVec x :=
  (continuous_const.matrix_mulVec continuous_id).measurable

theorem smul_map_diagonal (μ : Measure F) [μ.IsAddHaarMeasure] {D : ι → F}
    (h : det (diagonal D) ≠ 0) :
    (∏ i, (‖D i‖₊ : ℝ≥0∞)) • Measure.map (fun x : ι → F => (diagonal D).mulVec x)
      (Measure.pi fun _ : ι => μ) = Measure.pi fun _ : ι => μ := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  simp only [Measure.coe_smul, smul_eq_mul, Pi.smul_apply]
  rw [Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have : ((fun x : ι → F => (diagonal D).mulVec x) ⁻¹' Set.pi Set.univ fun i : ι => s i) =
      Set.pi Set.univ fun i : ι => (fun y => D i * y) ⁻¹' s i := by
    ext f
    simp only [mem_univ_pi, mem_preimage, mulVec_diagonal]
  have B : ∀ i, (‖D i‖₊ : ℝ≥0∞) * μ ((fun y => D i * y) ⁻¹' s i) = μ (s i) := by
    intro i
    have A : D i ≠ 0 := by
      simp only [det_diagonal, Ne] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [measure_preimage_mul_left μ _ A, ← mul_assoc,
      ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 A)) ENNReal.coe_ne_top,
      one_mul]
  rw [this, Measure.pi_pi, ← Finset.prod_mul_distrib]
  simp only [B]

theorem map_transvection (μ : Measure F) [μ.IsAddHaarMeasure] (t : TransvectionStruct ι F) :
    Measure.map (fun x : ι → F => t.toMatrix.mulVec x) (Measure.pi fun _ : ι => μ) =
      Measure.pi fun _ : ι => μ := by
  have ht : Measurable fun x : ι → F => t.toMatrix.mulVec x := measurable_mulVec _
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ => hs i
  simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, add_mulVec, one_mulVec, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ => indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]

theorem map_mulVec (μ : Measure F) [μ.IsAddHaarMeasure] {M : Matrix ι ι F} (hM : det M ≠ 0) :
    Measure.map (fun x : ι → F => M.mulVec x) (Measure.pi fun _ : ι => μ) =
      (‖M.det‖₊ : ℝ≥0∞)⁻¹ • Measure.pi fun _ : ι => μ := by
  apply diagonal_transvection_induction_of_det_ne_zero
    (fun M : Matrix ι ι F => Measure.map (fun x : ι → F => M.mulVec x) (Measure.pi fun _ : ι => μ) =
      (‖M.det‖₊ : ℝ≥0∞)⁻¹ • Measure.pi fun _ : ι => μ) M hM
  · intro D hD
    conv_rhs => rw [← smul_map_diagonal μ hD]
    rw [smul_smul]
    have hprod : (‖(diagonal D).det‖₊ : ℝ≥0∞) = ∏ i, (‖D i‖₊ : ℝ≥0∞) := by
      rw [det_diagonal, nnnorm_prod, ENNReal.coe_finsetProd]
    rw [hprod, ENNReal.inv_mul_cancel, one_smul]
    · rw [← hprod]; exact ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hD)
    · exact ENNReal.prod_ne_top fun _ _ => ENNReal.coe_ne_top
  · intro t
    rw [map_transvection μ t, TransvectionStruct.det, nnnorm_one, ENNReal.coe_one, inv_one, one_smul]
  · intro A B hA hB IHA IHB
    have hcomp : (fun x : ι → F => (A * B).mulVec x) =
        (fun x : ι → F => A.mulVec x) ∘ fun x : ι → F => B.mulVec x := by
      funext x; simp [mulVec_mulVec]
    rw [hcomp, ← Measure.map_map (measurable_mulVec A) (measurable_mulVec B), IHB,
      Measure.map_smul, IHA, smul_smul, det_mul, nnnorm_mul, ENNReal.coe_mul,
      ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.2 (nnnorm_ne_zero_iff.2 hA)))
        (Or.inl ENNReal.coe_ne_top), mul_comm]

omit [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)] in
theorem coe_nnnorm_inv_eq_ofReal {M : Matrix ι ι F} (hM : det M ≠ 0) :
    (‖M.det‖₊ : ℝ≥0∞)⁻¹ = ENNReal.ofReal ‖M.det‖⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 hM), ofReal_norm, enorm_eq_nnnorm]

end KcAdicLinCV

open KcAdicLinCV in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (v.adicCompletion K)) (hM : M.det ≠ 0) :
    Measure.map (fun x : ι → v.adicCompletion K => M.mulVec x) (Measure.pi fun _ : ι => μ) =
      ENNReal.ofReal ‖M.det‖⁻¹ • Measure.pi fun _ : ι => μ := by
  rw [map_mulVec μ hM, coe_nnnorm_inv_eq_ofReal hM]

end S_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi
end P2MW
export P2MW.S_NumberField_AdicCompletion_map_matrix_mulVec_pi_eq_smul_pi (solution)
