-- Prove2me | solution 1 for GlobalTheory.SplitFlip.hasDepth_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:08:12.359918+00:00
-- url     : https://prove2.me/submissions/05b11c3c-5c14-47fb-97f0-e6fdd66e3673

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_pow_smul_le

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
omit [Fintype D] [DecidableEq D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) :
    HasDepth ϖ e Λ ((matLat A Λ : Set (Matrix A D k)).indicator 1) := by
  refine ⟨fun X hX => Set.indicator_of_notMem hX _, fun X Z hZ => ?_⟩
  have hZ' : Z ∈ matLat A Λ := fun i => pow_smul_le hϖ e Λ (hZ i)
  by_cases hX : X ∈ matLat A Λ
  · rw [Set.indicator_of_mem (add_mem hX hZ'), Set.indicator_of_mem hX]; rfl
  · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem (fun h => hX ((add_mem_cancel_right hZ').1 h))]
end GlobalTheory.SplitFlip
