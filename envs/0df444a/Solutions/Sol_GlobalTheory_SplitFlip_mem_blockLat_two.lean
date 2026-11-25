-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_blockLat_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:14:37.680478+00:00
-- url     : https://prove2.me/submissions/90a49076-1aa9-4113-8897-ed3bbb0fbecc

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
variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) (e : ℕ) (x : D₁ ⊕ D₂ → k) :
    x ∈ blockLat ϖ e (Assignment.two.block D₁ D₂) ↔ (∀ j, valuation k (x (.inl j)) ≤ 1) ∧
      ∀ j, valuation k (x (.inr j)) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by
  simp [blockLat, mem_diagLat, blockUnits, Assignment.block]
end GlobalTheory.SplitFlip
