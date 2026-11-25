-- Prove2me | solution 1 for GlobalTheory.BadShare.tupleWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:01:34.718119+00:00
-- url     : https://prove2.me/submissions/9280fc74-5ff0-431d-a3f2-d244bc257385

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_OneSubTwoDivLeSquarefreeLabelMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassRootsNotDistinctLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GoodSquarefreeLabelTuplesWeightGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime]
variable {g} {ι : Type} [Fintype ι] {N : ℕ}
namespace GlobalTheory.BadShare
theorem _root_.solution (F : ι → (ZMod g)[X]) : 0 ≤ ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  exact Finset.prod_nonneg fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)
end GlobalTheory.BadShare
