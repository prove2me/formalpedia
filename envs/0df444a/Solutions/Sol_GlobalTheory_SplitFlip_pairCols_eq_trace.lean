-- Prove2me | solution 1 for GlobalTheory.SplitFlip.pairCols_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:19:16.480993+00:00
-- url     : https://prove2.me/submissions/d9c3f07a-eb6f-434f-8c59-d60fa78d065a

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
variable {A D : Type*}
variable [DecidableEq D]
variable [Fintype A]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) :
    pairCols P Y T = trace (T * (Y.submatrix id (Subtype.val : P → D))ᵀ) := by
  simp [pairCols, trace, Matrix.mul_apply]
end GlobalTheory.SplitFlip
