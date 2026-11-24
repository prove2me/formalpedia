-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_dualLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:54:46.130382+00:00
-- url     : https://prove2.me/submissions/daf285c1-65ad-40b8-8449-624d54966863

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution {Λ : Submodule 𝒪[k] (D → k)} {x : D → k} : x ∈ dualLat Λ ↔ ∀ y ∈ Λ, x ⬝ᵥ y ∈ 𝒪[k] := by
  refine forall₂_congr fun y _ => ?_
  rw [Submodule.mem_one]
  exact ⟨by rintro ⟨r, hr⟩; exact (show (r : k) = x ⬝ᵥ y from hr) ▸ r.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
end GlobalTheory.SplitFlip
