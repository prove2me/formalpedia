-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.gW_joinCol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:04:55.48394+00:00
-- url     : https://prove2.me/submissions/9309f7be-3e4f-4073-8abd-7438249de053

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


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
theorem _root_.solution {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α) (c : Fin d → ℂ)
    (C : Fin d → {j : α // j ≠ j₀} → ℂ) :
    gW d α (joinCol j₀ c C) =
      gW d {j : α // j ≠ j₀} C * ENNReal.ofReal (Real.exp (-∑ k, ‖c k‖ ^ 2)) := by
  unfold gW
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [← neg_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp [joinCol, j.2]
  · simp [joinCol]
end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
