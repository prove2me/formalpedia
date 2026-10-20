-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.constant_on_row_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:27:48.555456+00:00
-- url     : https://prove2.me/submissions/3a5846d3-87d3-4ed8-b4c5-d60bffd1ec2a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean:L97-L133
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.constant_on_row_fiber. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedGaps ----
namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- For a monotone row map, equality on adjoining entries in a row implies
equality throughout that row's matching fiber. -/
theorem constant_on_row_fiber {n : ℕ} (R S : Fin (n + 1) → ℕ)
    (hR : Monotone R) (r : ℕ)
    (hstep : ∀ i : Fin n, R i.castSucc = r → R i.succ = r →
      S i.castSucc = S i.succ) :
    ∀ i j, R i = r → R j = r → S i = S j := by
  have hordered : ∀ j : Fin (n + 1), ∀ i, i ≤ j → R i = r → R j = r →
      S i = S j := by
    intro j
    induction j using Fin.induction with
    | zero =>
        intro i hi _ _
        have : i = 0 := le_antisymm hi (Fin.zero_le i)
        subst i
        rfl
    | succ j ih =>
        intro i hij hir hjr
        by_cases heq : i = j.succ
        · subst i; rfl
        have hip : i ≤ j.castSucc := by
          apply Fin.le_iff_val_le_val.2
          have hh := Fin.le_iff_val_le_val.1 hij
          have hn : i.val ≠ j.succ.val := by
            intro h
            exact heq (Fin.ext h)
          simp only [Fin.val_succ, Fin.val_castSucc] at *
          omega
        have hpr : R j.castSucc = r := by
          have hlo := hR hip
          have hhi := hR (show j.castSucc ≤ j.succ by exact Fin.le_iff_val_le_val.2 (Nat.le_succ _))
          omega
        exact (ih i hip hir hpr).trans (hstep j hpr hjr)
  intro i j hi hj
  rcases le_total i j with hij | hji
  · exact hordered j i hij hi hj
  · exact (hordered i j hji hj hi).symm

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.constant_on_row_fiber := @_root_.OAI.TreeEdit.BinaryLower.Tagged.constant_on_row_fiber
