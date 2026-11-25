-- Prove2me | solution 1 for GlobalTheory.T.gramDet_inequalities_closed_forms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:54:27.206476+00:00
-- url     : https://prove2.me/submissions/0afa26ee-a3e3-4860-936e-bace1e62de5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Theorems.Thm_GlobalTheory_gramDet_closed_forms


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
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (m α β γ : Type) [Fintype m] [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (M : Matrix m (α ⊕ β ⊕ γ) ℂ), (((M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.inl : α → α ⊕ β ⊕ γ))).det.re) * (((M)ᴴ * (M)).det.re) ≤ (((M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ))).det.re) * (((M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))ᴴ * (M.submatrix id (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ))).det.re)) ∧ (∀ (r : ℕ) (a : Matrix (Fin r) (Fin r) ℂ), ∃ ω : ℝ, 1 ≤ ω ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix (Fin r) ι ℂ), (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re)) ∧ (∀ (r : ℕ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ ω ∧ ∀ (i : ℕ) (M : Matrix (Fin r) (Fin i) ℂ), 0 < (((M)ᴴ * (M)).det.re) → (∀ a ∈ S, (((a * M)ᴴ * (a * M)).det.re) ≤ ω * (((M)ᴴ * (M)).det.re) ∧ (((M)ᴴ * (M)).det.re) ≤ ω * (((a * M)ᴴ * (a * M)).det.re)) ∧ (0 < i → i < r → ∑ a ∈ S, ((((a * M)ᴴ * (a * M)).det.re) / (((M)ᴴ * (M)).det.re)) ^ (-δ) ≤ S.card * c)) ∧ (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  first | exact @GlobalTheory.gramDet_closed_forms | exact GlobalTheory.gramDet_closed_forms | (intros; apply GlobalTheory.gramDet_closed_forms <;> assumption)
end _root_.GlobalTheory.T
