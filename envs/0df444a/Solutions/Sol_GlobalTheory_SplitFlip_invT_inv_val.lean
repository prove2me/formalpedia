-- Prove2me | solution 1 for GlobalTheory.SplitFlip.invT_inv_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:06.455874+00:00
-- url     : https://prove2.me/submissions/5cbe71cd-5025-4a10-9752-0cf7578e574d

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (h : GL D k) : ((invT h)⁻¹).val = h.valᵀ := rfl
end GlobalTheory.SplitFlip
