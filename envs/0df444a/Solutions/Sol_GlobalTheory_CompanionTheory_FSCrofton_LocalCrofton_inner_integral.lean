-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.inner_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:46:54.301535+00:00
-- url     : https://prove2.me/submissions/e125022d-5b7b-432f-aba2-104cc3401445

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_gW_ne_top
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_measurable_gauss
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_gW_joinCol
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_joinCol_zero_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_differentiableOn_quot
import Theorems.Thm_GlobalTheory_T_change_variables_zero_count
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d


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
theorem _root_.solution (d : ℕ) (α : Type) [Fintype α] [DecidableEq α] (j₀ : α) (U A : Set (V d))
    (b : α → V d → ℂ) (hU : IsOpen U) (hb : ∀ j, DifferentiableOn ℂ (b j) U)
    (hne : ∀ z ∈ U, b j₀ z ≠ 0) (hAU : A ⊆ U) (hAm : MeasurableSet A)
    (g : {j : α // j ≠ j₀} → V d → ℂ) (hgA : ∀ j, ∀ z ∈ A, g j z = b j.1 z / b j₀ z)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    ∫⁻ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      ∫⁻ z in A, gW d {j : α // j ≠ j₀} C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * g j z‖ ^ 2) *
          ‖(Matrix.of C * (Matrix.of fun j a =>
            fderiv ℂ (fun v => b (j : {j : α // j ≠ j₀}).1 v / b j₀ v) z
              (EuclideanSpace.single a 1) : Matrix {j : α // j ≠ j₀} (Fin d) ℂ)).det‖ ^ 2) := by
  have hf : ∀ j : {j : α // j ≠ j₀}, DifferentiableOn ℂ (fun v => b j.1 v / b j₀ v) U :=
    fun j => differentiableOn_quot U b hb j₀ hne j.1
  have e1 : ∀ c : Fin d → ℂ, gW d α (joinCol j₀ c C) * zeroCnt d A b (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * (ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) *
        (({z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0}.encard :
          ℕ∞) : ℝ≥0∞)) := by
    intro c
    have hs : {z ∈ A | ∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0} =
        {z ∈ A | ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0} := by
      ext z
      simp only [Set.mem_setOf_eq]
      refine and_congr_right fun hz => ?_
      exact joinCol_zero_iff j₀ c C b z (hne z (hAU hz))
    rw [gW_joinCol, mul_assoc]
    unfold zeroCnt
    rw [hs]
  simp_rw [e1]
  rw [lintegral_const_mul' _ _ (gW_ne_top d _ C),
    GlobalTheory.T.change_variables_zero_count d {j : α // j ≠ j₀} U A (fun j v => b j.1 v / b j₀ v) C
      (fun c => ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2))) hU hf hAU hAm (measurable_gauss d),
    ← lintegral_const_mul' _ _ (gW_ne_top d _ C)]
  refine setLIntegral_congr_fun hAm fun z hz => ?_
  simp only [norm_neg]
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp only [hgA _ z hz]
end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
