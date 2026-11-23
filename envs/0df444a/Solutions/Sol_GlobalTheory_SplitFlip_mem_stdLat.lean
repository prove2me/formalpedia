-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:03.031829+00:00
-- url     : https://prove2.me/submissions/d34d4963-b0ad-42fa-92d1-590e5e3a4e57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_diagLat

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution {x : D → k} : x ∈ stdLat k D ↔ ∀ j, x j ∈ 𝒪[k] := by
  simp [stdLat, mem_diagLat, Valuation.mem_integer_iff]
end GlobalTheory.SplitFlip
