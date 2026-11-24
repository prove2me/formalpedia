-- Prove2me | solution 1 for GlobalTheory.T.measurable_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:05.372695+00:00
-- url     : https://prove2.me/submissions/59bf9321-d0e8-40e6-91a4-6bb58b98b06d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCountStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurable_zeroCnt


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ), (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A → Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | exact GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt <;> assumption)
end _root_.GlobalTheory.T
