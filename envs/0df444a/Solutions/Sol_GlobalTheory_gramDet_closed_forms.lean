-- Prove2me | solution 1 for GlobalTheory.gramDet_closed_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:46:22.688909+00:00
-- url     : https://prove2.me/submissions/71c2a2a4-3e87-4090-a009-512d2bd92368

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsDetAddEqDetMulDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetCauchySchwarzOfDetMono
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsScalarSubPosSemidef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetRePosIffInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UniformLogExpansionOfPointwise
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsRpowNegSumLeOfSumLog
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OffDiagonalMatrixUnitsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedForms
import Theorems.Thm_GlobalTheory_det_re_mono_of_posSemidef
import Theorems.Thm_GlobalTheory_exists_finite_symmetric_irreducible_rotations
import Theorems.Thm_GlobalTheory_exists_rpow_neg_sum_le_of_sum_log
import Theorems.Thm_GlobalTheory_gramDet_contraction
import Theorems.Thm_GlobalTheory_gram_det_cauchy_schwarz_of_det_mono
import Theorems.Thm_GlobalTheory_gram_det_mul_le
import Theorems.Thm_GlobalTheory_gram_det_submodular
import Theorems.Thm_GlobalTheory_offDiagonal_matrixUnits_irreducible
import Theorems.Thm_GlobalTheory_sum_log_gramDet_ratio_pos
import Theorems.Thm_GlobalTheory_uniform_log_expansion_of_pointwise


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) ∧ (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) ∧ (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) ∧ (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  have hmono := det_re_mono_of_posSemidef
  have hcs := gram_det_cauchy_schwarz_of_det_mono hmono
  have hdist := gram_det_mul_le hmono
  have hexp := uniform_log_expansion_of_pointwise (sum_log_gramDet_ratio_pos hcs)
  refine ⟨gram_det_submodular hmono, hdist, ?_, ?_⟩
  · exact gramDet_contraction hdist hexp exists_rpow_neg_sum_le_of_sum_log
  · exact exists_finite_symmetric_irreducible_rotations offDiagonal_matrixUnits_irreducible
end GlobalTheory
