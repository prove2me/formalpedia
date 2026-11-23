-- Prove2me | solution 1 for GlobalTheory.SplitFlip.frameMatrixFirstColumnBlock_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:46.55804+00:00
-- url     : https://prove2.me/submissions/87dbf933-43d1-47e6-9072-2440125f4577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

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
theorem _root_.solution {B : Type*} (σ : A ⊕ A' ≃ D) (M : Matrix D B k) (i : A) (j : B) :
    (X0 k σ * M) i j = M (σ (Sum.inl i)) j := by simp [X0, Matrix.mul_apply]
end GlobalTheory.SplitFlip
