-- Prove2me | solution 1 for GlobalTheory.SplitFlip.frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:35.736313+00:00
-- url     : https://prove2.me/submissions/af307893-855e-4ed5-a068-34be2c60e101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_invT_val
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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
namespace GlobalTheory.SplitFlip
theorem _root_.solution (σ : A ⊕ A' ≃ D) (h : GL D k) :
    (Y0 k σ * h.val) * (X0 k σ * (invT h).val)ᵀ = 0 := by
  rw [transpose_mul, invT_val, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv,
    Matrix.one_mul]
  ext i j; simp [frameMatrixSecondColumnBlock_mul_apply, X0]
end GlobalTheory.SplitFlip
