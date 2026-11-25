-- Prove2me | solution 1 for GlobalTheory.BadShare.tupleMass_single_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:48.949607+00:00
-- url     : https://prove2.me/submissions/6800abb1-9750-4717-9e54-6743889c0ebf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassDivisorBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_OneSubTwoDivLeSquarefreeLabelMassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassRootsNotDistinctLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassHasDivisorOfDegreeLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GoodSquarefreeLabelTuplesWeightGe
import Theorems.Thm_GlobalTheory_BadShare_tupleMass_forall

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
theorem _root_.solution (h1 : (mass g N fun _ => True) ≤ 1) (v : ι) (A : (ZMod g)[X] → Prop) :
    tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) ≤ mass g N A := by
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have key : tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) =
      tupleMass g N (fun F => ∀ w, (if w = v then A else fun _ => True) (F w)) := by
    unfold tupleMass
    refine Finset.sum_congr rfl fun F _ => ?_
    have hiff : A (F v) ↔ ∀ w, (if w = v then A else fun _ => True) (F w) :=
      ⟨fun h w => by by_cases hw : w = v <;> simp_all, fun h => by simpa using h v⟩
    by_cases h : A (F v)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (mt hiff.mpr h)]
  rw [key, tupleMass_forall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl]
  have hrest : ∏ w ∈ Finset.univ.erase v, mass g N (if w = v then A else fun _ => True) ≤ 1 := by
    apply Finset.prod_le_one
    · exact fun w _ => hm _
    · intro w hw
      rw [if_neg (Finset.ne_of_mem_erase hw)]
      exact h1
  calc mass g N A * _ ≤ mass g N A * 1 := mul_le_mul_of_nonneg_left hrest (hm A)
    _ = _ := mul_one _
end GlobalTheory.BadShare
