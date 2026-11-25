-- Prove2me | solution 1 for GlobalTheory.BadShare.tupleMass_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:25.303833+00:00
-- url     : https://prove2.me/submissions/ad6bc629-8ffe-4cf2-a70e-983317276ea5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_OneSubTwoDivLeSquarefreeLabelMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassRootsNotDistinctLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GoodSquarefreeLabelTuplesWeightGe
import Theorems.Thm_GlobalTheory_BadShare_tupleWeight_nonneg

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
theorem _root_.solution {κ : Type} (s : Finset κ) (Q : κ → (ι → (ZMod g)[X]) → Prop) :
    tupleMass g N (fun F => ∃ i ∈ s, Q i F) ≤ ∑ i ∈ s, tupleMass g N (Q i) := by
  unfold tupleMass
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun F _ => ?_
  have hz : ∀ j ∈ s, 0 ≤ (if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := fun j _ => by
    split_ifs
    · exact tupleWeight_nonneg F
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hQ⟩ := h
    calc ∏ v, ((torusCard g (F v) : ℝ))⁻¹ = (if Q i F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := by rw [if_pos hQ]
      _ ≤ ∑ j ∈ s, if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0 :=
        Finset.single_le_sum (f := fun j => if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) hz hi
  · exact Finset.sum_nonneg hz
end GlobalTheory.BadShare
