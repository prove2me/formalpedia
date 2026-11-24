-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FSCrofton.measurable_zeroCnt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:36:14.757339+00:00
-- url     : https://prove2.me/submissions/07ea2161-c5bf-4c78-a9f4-08d1ac52d2c3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MeasurableZeroCount
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_measurable_zeroCnt_of_continuousOn

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton
open TopologicalSpace
variable {X : Type} [TopologicalSpace X] {d : ℕ} {α : Type} [Fintype α]
namespace GlobalTheory.CompanionTheory.FSCrofton
theorem _root_.solution : ∀ (d : ℕ) (α : Type) [Fintype α] (U A : Set (V d)) (b : α → V d → ℂ),
    (∀ j, ContinuousOn (b j) U) → A ⊆ U → IsSigmaCompact A →
      Measurable (zeroCnt d A b : (Fin d → α → ℂ) → ℝ≥0∞) := by
  intro d α _ U A b hb hAU hA
  exact measurable_zeroCnt_of_continuousOn hA fun j => (hb j).mono hAU
end GlobalTheory.CompanionTheory.FSCrofton
