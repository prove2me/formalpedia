-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.isTensor_pureTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:55.618291+00:00
-- url     : https://prove2.me/submissions/b894dcad-e5f3-4822-bf9d-9251672a9f33

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
open GlobalTheory.SplitFlip.Grid
variable (G : Grid k)
namespace GlobalTheory.SplitFlip.Grid
theorem _root_.solution (ϖ : kˣ) (e : ℕ) (γ : List Edge)
    (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) (hφ : ∀ b ∈ γ, IsNatDatum ϖ e (φ b)) :
    G.IsTensor ϖ e γ (G.lines₂ γ φ) := by
  refine ⟨fun x y h => ?_, fun x b hb hx => ?_, fun x z hz => ?_⟩
  · exact congrArg List.prod (List.map_congr_left fun b hb => by rw [h b hb])
  · exact List.prod_eq_zero (List.mem_map.2 ⟨b, hb, (hφ b hb).1 _ hx⟩)
  · exact congrArg List.prod (List.map_congr_left fun b hb => (hφ b hb).2 _ _ (hz b))
end GlobalTheory.SplitFlip.Grid
