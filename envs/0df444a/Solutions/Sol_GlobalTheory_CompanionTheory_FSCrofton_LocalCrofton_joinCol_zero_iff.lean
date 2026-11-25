-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton.joinCol_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:28.215804+00:00
-- url     : https://prove2.me/submissions/a81af438-7fd3-4b83-aafa-5ac700565820

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogFubiniStudyStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ComplexHessianLogDehomogeniseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralSplitColumnStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RandomSectionZeroCount
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
theorem _root_.solution {X : Type} {d : ℕ} {α : Type} [Fintype α] [DecidableEq α] (j₀ : α)
    (c : Fin d → ℂ) (C : Fin d → {j : α // j ≠ j₀} → ℂ) (b : α → X → ℂ) (z : X)
    (hz : b j₀ z ≠ 0) :
    (∀ k, ∑ j, joinCol j₀ c C k j * b j z = 0) ↔
      ∀ k, c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z) = 0 := by
  refine forall_congr' fun k => ?_
  have h : ∑ j, joinCol j₀ c C k j * b j z =
      b j₀ z * (c k + ∑ j : {j : α // j ≠ j₀}, C k j * (b j.1 z / b j₀ z)) := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, mul_add, Finset.mul_sum]
    congr 1
    · simp [joinCol, mul_comm]
    · refine Finset.sum_congr rfl fun j _ => ?_
      simp only [joinCol, j.2, dite_false]
      field_simp
  rw [h, mul_eq_zero]
  simp [hz]
end GlobalTheory.CompanionTheory.FSCrofton.LocalCrofton
