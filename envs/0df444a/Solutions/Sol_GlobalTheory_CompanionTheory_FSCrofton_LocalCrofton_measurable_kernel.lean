-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.measurable_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:48:35.005673+00:00
-- url     : https://prove2.me/submissions/64a89165-3b2c-4dfd-bbcf-de8e99f4ae65

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
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_LocalCrofton_continuous_kernel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
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
theorem _root_.solution {X : Type} [MeasurableSpace X] (d : ℕ) (β : Type) [Fintype β]
    (g : β → X → ℂ) (F : β → Fin d → X → ℂ) (hg : ∀ j, Measurable (g j))
    (hF : ∀ j a, Measurable (F j a)) :
    Measurable fun p : (Fin d → β → ℂ) × X =>
      gW d β p.1 * ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, p.1 k j * g j p.2‖ ^ 2) *
        ‖(Matrix.of p.1 * (Matrix.of fun j a => F j a p.2 : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  have hm : Measurable fun p : (Fin d → β → ℂ) × X =>
      ((p.1, (fun j => g j p.2), (fun j a => F j a p.2)) :
        (Fin d → β → ℂ) × ((β → ℂ) × (β → Fin d → ℂ))) := by
    refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
    · exact measurable_pi_lambda _ fun j => (hg j).comp measurable_snd
    · exact measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun a =>
        (hF j a).comp measurable_snd
  have hq := (continuous_kernel d β).measurable.comp hm
  exact ((measurable_gW d β).comp measurable_fst).mul (ENNReal.measurable_ofReal.comp hq)
end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
