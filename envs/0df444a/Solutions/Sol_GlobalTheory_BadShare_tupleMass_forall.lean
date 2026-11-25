-- Prove2me | solution 1 for GlobalTheory.BadShare.tupleMass_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:24.080311+00:00
-- url     : https://prove2.me/submissions/dee97ba7-8185-4f5a-935d-3d6ca19282c2

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
theorem _root_.solution (A : ι → (ZMod g)[X] → Prop) :
    tupleMass g N (fun F => ∀ v, A v (F v)) = ∏ v, mass g N (A v) := by
  unfold tupleMass mass
  simp_rw [Finset.sum_filter]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  split_ifs with h
  · exact Finset.prod_congr rfl fun v _ => (if_pos (h v)).symm
  · push Not at h
    obtain ⟨v, hv⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm
end GlobalTheory.BadShare
