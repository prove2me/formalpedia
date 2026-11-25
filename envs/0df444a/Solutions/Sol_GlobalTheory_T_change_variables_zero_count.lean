-- Prove2me | solution 1 for GlobalTheory.T.change_variables_zero_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:55.357297+00:00
-- url     : https://prove2.me/submissions/55fd1661-81d6-4582-821b-79e6d851abb7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCount
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCountStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_area_formula_neg_comb


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
theorem _root_.solution : ∀ (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ) (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞), IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → A ⊆ U → MeasurableSet A → Measurable h → ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) = ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) * ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb | exact GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb | (intros; apply GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb <;> assumption)
end _root_.GlobalTheory.T
