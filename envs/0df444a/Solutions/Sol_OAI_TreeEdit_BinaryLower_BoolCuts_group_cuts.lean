-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.BoolCuts.group_cuts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:24:44.478327+00:00
-- url     : https://prove2.me/submissions/db02abc1-7172-4990-8c90-5fba146de0b1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/ScalarCutsBool.lean:L72-L112
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.BoolCuts.group_cuts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

-- ---- from OAI.Combinatorics.BinaryEdit.ScalarCutsBool ----
namespace OAI

/-! Scalar finite cut decomposition used by the finite-group obstruction.
This is the one-real-coordinate part of `lem:cuts` in preliminaries.tex. -/

namespace TreeEdit.BinaryLower.BoolCuts

open scoped BigOperators

lemma cutDistance_const {S : Type*} (b : Bool) (x y : S) :
    cutDistance (fun _ => b) x y = 0 := by simp [cutDistance]

/-- Group an arbitrary finite collection of cuts by the Boolean function it defines.
The two trivial cuts are discarded, since their distances vanish. -/
lemma group_cuts {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I]
    (C : I → S → Bool) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ a : (S → Bool) → ℝ,
      (∀ D, 0 ≤ a D) ∧
      (∀ x y, ∑ i, w i * cutDistance (C i) x y =
        ∑ D, a D * cutDistance D x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 := by
  classical
  let raw : (S → Bool) → ℝ := fun D => ∑ i with C i = D, w i
  let a : (S → Bool) → ℝ := fun D =>
    if D = (fun _ => false) ∨ D = (fun _ => true) then 0 else raw D
  refine ⟨a, ?_, ?_, ?_, ?_⟩
  · intro D
    dsimp [a]
    split_ifs
    · exact le_refl _
    · exact Finset.sum_nonneg (fun i _ => hw i)
  · intro x y
    have hraw : (∑ D, raw D * cutDistance D x y) =
        ∑ i, w i * cutDistance (C i) x y := by
      simp only [raw, Finset.sum_mul]
      calc
        _ = ∑ D, ∑ i with C i = D, w i * cutDistance (C i) x y := by
          apply Finset.sum_congr rfl
          intro D hD
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        _ = _ := Finset.sum_fiberwise Finset.univ C
          (fun i => w i * cutDistance (C i) x y)
    rw [← hraw]
    apply Finset.sum_congr rfl
    intro D hD
    dsimp [a]
    split_ifs with h
    · rcases h with rfl | rfl <;> simp [cutDistance_const]
    · rfl
  · simp [a]
  · simp [a]

end TreeEdit.BinaryLower.BoolCuts

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.BoolCuts
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.BoolCuts.group_cuts := @_root_.OAI.TreeEdit.BinaryLower.BoolCuts.group_cuts
