-- Prove2me | solution 1 for GlobalTheory.SplitFlip.mem_blockLat_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:50.540064+00:00
-- url     : https://prove2.me/submissions/bacafd31-d50f-4bf6-ae5e-e9869eb5e4de

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
    x ∈ blockLat ϖ e (Assignment.one.block D₁ D₂) ↔
      (∀ j, valuation k (x (.inl j)) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k)) ∧ ∀ j, valuation k (x (.inr j)) ≤ 1 := by
  simp [blockLat, mem_diagLat, blockUnits, Assignment.block]
end GlobalTheory.SplitFlip
