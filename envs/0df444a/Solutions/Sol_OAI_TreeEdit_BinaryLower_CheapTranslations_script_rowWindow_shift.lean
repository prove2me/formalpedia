-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.CheapTranslations.script_rowWindow_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:45:15.315026+00:00
-- url     : https://prove2.me/submissions/1807c340-9005-46a2-9e71-15ac41403c50

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CheapTranslations.lean:L126-L149
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.CheapTranslations.script_rowWindow_shift. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations

-- ---- from OAI.Combinatorics.BinaryEdit.CheapTranslations ----
namespace OAI

/-!
# Inexpensive translations

Elementary unrestricted edit scripts give the translation estimates in
`lem:finite-cost`.
-/

namespace TreeEdit.BinaryLower.CheapTranslations

universe u v

variable {α : Type u}

theorem unitEdit_prefix {x y : List α} (p : List α)
    (h : EditStep x y) : EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q s a =>
      simpa only [List.append_assoc] using EditStep.insert (p ++ q) s a
  | delete q s a =>
      simpa only [List.append_assoc] using EditStep.delete (p ++ q) s a
  | substitute q s a b =>
      simpa only [List.append_assoc] using EditStep.substitute (p ++ q) s a b

theorem script_prefix {x y : List α} {n : ℕ} (p : List α)
    (h : EditScript x y n) : EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil x => exact EditScript.nil _
  | cons step tail ih => exact EditScript.cons (unitEdit_prefix p step) ih

theorem script_trans {x y z : List α} {m n : ℕ}
    (hxy : EditScript x y m) (hyz : EditScript y z n) :
    EditScript x z (m + n) := by
  induction hxy with
  | nil x => simpa using hyz
  | cons step tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        EditScript.cons step (ih hyz)

theorem script_delete_prefix (p x : List α) :
    EditScript (p ++ x) x p.length := by
  induction p with
  | nil => exact EditScript.nil x
  | cons a p ih =>
      exact EditScript.cons (EditStep.delete [] (p ++ x) a) ih

theorem script_insert_prefix (p x : List α) :
    EditScript x (p ++ x) p.length := by
  induction p with
  | nil => exact EditScript.nil x
  | cons a p ih =>
      exact EditScript.cons (EditStep.insert [] x a) (script_prefix [a] ih)

theorem script_insert_suffix (x s : List α) :
    EditScript x (x ++ s) s.length := by
  simpa using script_prefix x (script_insert_prefix s [])

theorem rowWindow_add (rows : ℕ → List α) (a m n : ℕ) :
    rowWindow rows a (m + n) =
      rowWindow rows a m ++ rowWindow rows (a + m) n := by
  unfold rowWindow
  rw [← List.range'_append_1, List.flatMap_append]

theorem rowWindow_length (rows : ℕ → List α) (a n B : ℕ)
    (hlen : ∀ j, (rows j).length = B) :
    (rowWindow rows a n).length = n * B := by
  induction n generalizing a with
  | zero => simp [rowWindow]
  | succ n ih =>
      simp only [rowWindow, List.range'_succ, List.flatMap_cons,
        List.length_append, hlen]
      change B + (rowWindow rows (a + 1) n).length = (n + 1) * B
      rw [ih]
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]

/-- An explicit script for sliding a fixed number of rows. Its exact cost is
useful when the same local operation is repeated in a larger concatenation. -/
theorem script_rowWindow_shift (rows : ℕ → List α)
    (a T s B : ℕ) (hs : s ≤ T)
    (hlen : ∀ j, (rows j).length = B) :
    EditScript (rowWindow rows a T) (rowWindow rows (a + s) T)
      (2 * s * B) := by
  have hleft := rowWindow_add rows a s (T - s)
  have hright := rowWindow_add rows (a + s) (T - s) s
  rw [Nat.add_sub_of_le hs] at hleft
  rw [Nat.sub_add_cancel hs] at hright
  rw [hleft, hright]
  have h := script_trans
    (script_delete_prefix (rowWindow rows a s)
      (rowWindow rows (a + s) (T - s)))
    (script_insert_suffix (rowWindow rows (a + s) (T - s))
      (rowWindow rows (a + s + (T - s)) s))
  have hcost : (rowWindow rows a s).length +
      (rowWindow rows (a + s + (T - s)) s).length = 2 * s * B := by
    rw [rowWindow_length rows a s B hlen,
      rowWindow_length rows (a + s + (T - s)) s B hlen]
    simp only [two_mul, Nat.add_mul]
  rw [hcost] at h
  exact h

end TreeEdit.BinaryLower.CheapTranslations

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.CheapTranslations


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.CheapTranslations.script_rowWindow_shift.{u} := @_root_.OAI.TreeEdit.BinaryLower.CheapTranslations.script_rowWindow_shift.{u}
