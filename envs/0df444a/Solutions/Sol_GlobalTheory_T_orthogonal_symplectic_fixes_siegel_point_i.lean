-- Prove2me | solution 1 for GlobalTheory.T.orthogonal_symplectic_fixes_siegel_point_i
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:08:21.033668+00:00
-- url     : https://prove2.me/submissions/df7d9107-7b43-4858-a43d-cadf1865cfde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrthogonalSymplecticFixesSiegelPointI
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrthogonalSymplecticFixesSiegelPointIStatement
import Theorems.Thm_GlobalTheory_holPart_eq_and_gaussian_of_orthogonal_symplectic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → sᵀ * s = 1 → P.det ≠ 0 → GlobalTheory.Published.Metaplectic.holPart s = P ∧ ∀ x : l → ℝ, cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) = cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | exact GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic | (intros; apply GlobalTheory.holPart_eq_and_gaussian_of_orthogonal_symplectic <;> assumption)
end _root_.GlobalTheory.T
