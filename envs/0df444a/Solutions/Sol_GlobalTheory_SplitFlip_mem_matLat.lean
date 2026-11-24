-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_matLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:05.565255+00:00
-- url     : https://prove2.me/submissions/9c65170e-9989-4da0-9711-4e1aab2f702d

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution {Λ : Submodule 𝒪[k] (D → k)} {X : Matrix A D k} : X ∈ matLat A Λ ↔ ∀ i, X.row i ∈ Λ := Iff.rfl
end GlobalTheory.SplitFlip
