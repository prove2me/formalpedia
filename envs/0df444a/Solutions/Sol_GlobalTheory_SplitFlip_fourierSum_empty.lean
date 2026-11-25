-- Prove2me | solution 1 for GlobalTheory.SplitFlip.fourierSum_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:33.439253+00:00
-- url     : https://prove2.me/submissions/33334f89-87ef-44a0-98a3-b9906ac49469

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_fourierSum_apply

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
variable [DecidableEq A]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) :
    fourierSum ψ ϖ e ∅ Φ = Φ := by
  funext Y
  have h : ∀ T, setCols ∅ Y T = Y := fun T => by ext i j; simp [setCols]
  simp [fourierSum_apply, h, pairCols]
end GlobalTheory.SplitFlip
