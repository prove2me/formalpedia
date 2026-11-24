-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Model.pair_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:53.44593+00:00
-- url     : https://prove2.me/submissions/e755d28a-c5b5-4df8-aed1-53907a95663a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv

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
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A]
namespace GlobalTheory.SplitFlip.Model
theorem _root_.solution (Y : Matrix A (D₁ ⊕ D₂) k) (T : Matrix A (Assignment.two.block D₁ D₂) k) :
    pairCols _ Y T = ∑ i, ∑ j : D₂, setCols _ (0 : Matrix A (D₁ ⊕ D₂) k) T i (.inr j) * Y i (.inr j) := by
  unfold pairCols
  refine Finset.sum_congr rfl fun i _ => ?_
  symm
  refine Finset.sum_bij (fun j _ => ⟨.inr j, by simp [Assignment.block]⟩) (by simp)
    (fun a _ a' _ h => by simpa using congrArg Subtype.val h) ?_ ?_
  · rintro ⟨j | j, hj⟩ _
    · simp [Assignment.block] at hj
    · exact ⟨j, by simp, rfl⟩
  · intro j _; simp [setCols, Assignment.block]
end GlobalTheory.SplitFlip.Model
