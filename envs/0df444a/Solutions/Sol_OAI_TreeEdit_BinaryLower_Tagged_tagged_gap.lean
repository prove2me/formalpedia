-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.tagged_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:26:14.419562+00:00
-- url     : https://prove2.me/submissions/5e1253cf-9f35-41b5-af3a-a2a60594d595

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean:L58-L84
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.tagged_gap. The node keeps its source
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

/-- Equal row indices force the ordered tags of two source positions to be
nondecreasing. -/
theorem tag_le_of_same_row {a b m B : ℕ} (hab : a ≤ b)
    (hrow : a / B / m = b / B / m) :
    (a / B) % m ≤ (b / B) % m := by
  have hab' : a / B ≤ b / B := Nat.div_le_div_right hab
  have ha := Nat.mod_add_div (a / B) m
  have hb := Nat.mod_add_div (b / B) m
  rw [hrow] at ha
  omega

/-- A transition to a later target row, while staying in one source row,
forces at least `(m-1)*B` skipped target positions. -/
theorem tagged_gap {a b c d m B : ℕ} (hm : 1 ≤ m) (hB : 0 < B)
    (hab : a ≤ b) (hsource : a / B / m = b / B / m)
    (htarget : c / B / m < d / B / m)
    (htag₀ : (a / B) % m = (c / B) % m)
    (htag₁ : (b / B) % m = (d / B) % m) :
    c + 1 + (m - 1) * B ≤ d := by
  have htag : (c / B) % m ≤ (d / B) % m := by
    rw [← htag₀, ← htag₁]
    exact tag_le_of_same_row hab hsource
  have hc := Nat.mod_add_div (c / B) m
  have hd := Nat.mod_add_div (d / B) m
  have hmrow := Nat.mul_le_mul_left m (Nat.succ_le_of_lt htarget)
  have hblocks : c / B + m ≤ d / B := by nlinarith
  have hmul := Nat.mul_le_mul_left B hblocks
  have hc' := Nat.mod_add_div c B
  have hd' := Nat.mod_add_div d B
  have hrem := Nat.mod_lt c hB
  have hpred : m - 1 + 1 = m := by omega
  have heq := congrArg (fun t : ℕ => t * B) hpred
  calc
    c + 1 + (m - 1) * B = (c % B + 1) + B * (c / B) + (m - 1) * B := by omega
    _ ≤ B + B * (c / B) + (m - 1) * B := by omega
    _ = B * (c / B + m) := by nlinarith [heq]
    _ ≤ B * (d / B) := hmul
    _ ≤ d := by omega

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.tagged_gap := @_root_.OAI.TreeEdit.BinaryLower.Tagged.tagged_gap
