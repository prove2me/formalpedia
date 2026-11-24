-- Prove2me | solution 1 for GlobalTheory.SplitFlip.shellSet_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:36:28.476074+00:00
-- url     : https://prove2.me/submissions/d3224fc8-89b0-43bf-8757-fcb63a76a72e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_mem_shellSet

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) : shellSet ϖ (0 : A → ℤ) = KO k A := by
  have h1 : (diagGL fun i : A => ϖ ^ (0 : A → ℤ) i) = 1 := Units.ext (by simp)
  ext g
  rw [mem_shellSet, h1]
  exact ⟨by rintro ⟨x, hx, y, hy, rfl⟩; simpa using mul_mem hx hy, fun h => ⟨g, h, 1, one_mem _, by simp⟩⟩
end GlobalTheory.SplitFlip
