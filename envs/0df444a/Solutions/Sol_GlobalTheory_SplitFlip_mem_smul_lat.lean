-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_smul_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:07.039089+00:00
-- url     : https://prove2.me/submissions/457a2c8c-6214-48b7-a969-b97e4d12d161

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
theorem _root_.solution (c : kˣ) (Λ : Submodule 𝒪[k] (D → k)) (x : D → k) : x ∈ c • Λ ↔ c⁻¹ • x ∈ Λ := by
  refine (Submodule.mem_smul_pointwise_iff_exists x c Λ).trans ?_
  exact ⟨by rintro ⟨y, hy, rfl⟩; simpa using hy, fun h => ⟨_, h, by simp⟩⟩
end GlobalTheory.SplitFlip
