-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_glLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:42.035299+00:00
-- url     : https://prove2.me/submissions/de632f6b-103c-4d51-917b-d4472720caad

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
variable [Fintype D]
variable [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {Λ : Submodule 𝒪[k] (D → k)} {h : GL D k} : h ∈ glLat Λ ↔ ∀ x, x ᵥ* h.val ∈ Λ ↔ x ∈ Λ := Iff.rfl
end GlobalTheory.SplitFlip
