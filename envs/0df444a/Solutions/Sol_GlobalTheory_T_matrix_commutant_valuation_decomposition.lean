-- Prove2me | solution 1 for GlobalTheory.T.matrix_commutant_valuation_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:17.200778+00:00
-- url     : https://prove2.me/submissions/24e7f705-52d8-4642-8986-655b57fb7974

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommutantValuationDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixCommutantValuationDecompositionStatement
import Theorems.Thm_GlobalTheory_ValDecomp_valuation_decomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → (∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧ e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a) → ∀ c : Matrix (Fin n) (Fin n) E, IsUnit c → c * N = N * c → ∃ e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E, (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ ‖u.det‖ = 1 ∧ e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧ e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ e₁ + e₂ + e₃ = 1 ∧ c * e₁ = u * e₁ ∧ c * e₂ = ϖ • (a₂ * e₂) ∧ c⁻¹ * e₃ = ϖ • (a₃ * e₃) := by
  first | exact @GlobalTheory.ValDecomp.valuation_decomp | exact GlobalTheory.ValDecomp.valuation_decomp | (intros; apply GlobalTheory.ValDecomp.valuation_decomp <;> assumption)
end _root_.GlobalTheory.T
