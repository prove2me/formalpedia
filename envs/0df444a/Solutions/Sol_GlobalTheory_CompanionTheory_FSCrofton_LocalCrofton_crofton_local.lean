-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.crofton_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:42.026021+00:00
-- url     : https://prove2.me/submissions/ea874816-2f55-4409-9c1d-e2e9872be347

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_measurable_gW
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_measurable_kernel
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_differentiableOn_quot
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_inner_integral
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_const_arith
import Theorems.Thm_GlobalTheory_T_complex_hessian_log_dehomogenise
import Theorems.Thm_GlobalTheory_T_complex_hessian_log_fubini_study
import Theorems.Thm_GlobalTheory_T_gaussian_det_levi_integral
import Theorems.Thm_GlobalTheory_T_lintegral_split_column
import Theorems.Thm_GlobalTheory_T_measurable_zero_count
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
namespace GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
theorem _root_.solution : ∀ (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d)) (b : α → V d → ℂ), IsOpen U → (∀ j, DifferentiableOn ℂ (b j) U) → (∀ z ∈ U, b j₀ z ≠ 0) → A ⊆ U → IsSigmaCompact A → ∫⁻ C : Fin d → α → ℂ, gW d α C * zeroCnt d A b C = ENNReal.ofReal (Real.pi ^ (d * Fintype.card α)) * ∫⁻ z in A, ENNReal.ofReal ((d.factorial : ℝ) / Real.pi ^ d * (cHess d (fun v => ((Real.log (∑ j, ‖b j v‖ ^ 2) : ℝ) : ℂ)) z).det.re) := by
  intro d α _ _ j₀ U A b hU hb hne hAU hA
  classical
  have hAm : MeasurableSet A := by
    obtain ⟨K, hK, hKA⟩ := hA
    rw [← hKA]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  have hΦ : Measurable fun C : Fin d → α → ℂ => gW d α C * zeroCnt d A b C :=
    (measurable_gW d α).mul (GlobalTheory.T.measurable_zero_count d α U A b (fun j => (hb j).continuousOn) hAU hA)
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  obtain ⟨g, hg, hgA⟩ : ∃ g : {j : α // j ≠ j₀} → V d → ℂ, (∀ j, Measurable (g j)) ∧
      ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z := by
    refine ⟨fun j => U.piecewise (fun v => b j.1 v / b j₀ v) (fun _ => 0), fun j => ?_,
      fun j z hz => by simp [Set.piecewise, hAU hz]⟩
    exact (hf j).continuousOn.measurable_piecewise continuousOn_const hU.measurableSet
  have hF : ∀ (j : {j : α // j ≠ j₀}) (a : Fin d), Measurable fun z =>
      fderiv ℂ (fun v => b j.1 v / b j₀ v) z (EuclideanSpace.single a 1) :=
    fun j a => measurable_fderiv_apply_const ℂ _ _
  have hK := measurable_kernel d {j : α // j ≠ j₀} g _ hg hF
  rw [GlobalTheory.T.lintegral_split_column d α j₀ _ hΦ]
  simp_rw [inner_integral d α j₀ U A b hU hb hne hAU hAm g hgA]
  rw [lintegral_lintegral_swap (ν := volume.restrict A) hK.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  have hcard : Fintype.card α = Fintype.card {j : α // j ≠ j₀} + 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨j₀⟩
    omega
  have h1 := GlobalTheory.T.gaussian_det_levi_integral d {j : α // j ≠ j₀} (fun j => b j.1 z / b j₀ z)
    (Matrix.of fun j a => fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
      (EuclideanSpace.single a 1))
  rw [GlobalTheory.T.complex_hessian_log_dehomogenise d α j₀ U b hU hb hne z (hAU hz),
    GlobalTheory.T.complex_hessian_log_fubini_study d {j : α // j ≠ j₀} U (fun j v => b j.1 v / b j₀ v) hU hf z (hAU hz),
    ← const_arith d _ _ hcard, ← h1]
  simp only [hgA _ z hz]
end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
