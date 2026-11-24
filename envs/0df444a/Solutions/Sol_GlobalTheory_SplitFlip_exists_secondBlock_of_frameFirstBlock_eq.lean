-- Prove2me | solution 1 for GlobalTheory.SplitFlip.exists_secondBlock_of_frameFirstBlock_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:58.106814+00:00
-- url     : https://prove2.me/submissions/18a14948-bf0f-4568-99e3-3809e63ceacf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_invT_inv_val
import Theorems.Thm_GlobalTheory_SplitFlip_gdet_mul
import Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixFirstColumnBlock_mul_apply
import Theorems.Thm_GlobalTheory_SplitFlip_frameMatrixSecondColumnBlock_mul_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (σ : A ⊕ A' ≃ D) {h h' : GL D k} (H : X0 k σ * (invT h').val = X0 k σ * (invT h).val) :
    ∃ C : GL A' k, Y0 k σ * h'.val = C.val * (Y0 k σ * h.val) ∧ gdet h' = gdet C * gdet h := by
  obtain ⟨u, rfl⟩ : ∃ u, h' = u * h := ⟨h' * h⁻¹, by simp⟩
  have H1 : X0 k σ * u.valᵀ = X0 k σ := by
    have h1 := congrArg (· * ((invT h)⁻¹).val) H
    simp only [map_mul, Units.val_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h1
    rw [← invT_inv_val]
    nth_rewrite 1 [← h1]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have H2 : ∀ r i, u.val r (σ (Sum.inl i)) = if σ (Sum.inl i) = r then 1 else 0 := fun r i => by
    have h1 := congrFun (congrFun H1 i) r
    rw [frameMatrixFirstColumnBlock_mul_apply] at h1
    exact h1
  let C : Matrix A' A' k := Matrix.of fun i j => u.val (σ (Sum.inr i)) (σ (Sum.inr j))
  have hdet : u.val.det = C.det := by
    rw [← det_submatrix_equiv_self σ, show u.val.submatrix σ σ =
      fromBlocks 1 (Matrix.of fun i j => u.val (σ (Sum.inl i)) (σ (Sum.inr j))) 0 C from ?_,
      det_fromBlocks_zero₂₁, det_one, one_mul]
    ext (i | i) (j | j) <;> simp [H2, C, one_apply, eq_comm]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero C (hdet ▸ u.det_ne_zero), ?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    congr 1
    ext i j
    obtain ⟨j | j, rfl⟩ := σ.surjective j <;> simp [frameMatrixSecondColumnBlock_mul_apply, H2, Matrix.mul_apply, Y0, C]
  · rw [gdet_mul]; congr 1; exact Units.ext hdet
end GlobalTheory.SplitFlip
