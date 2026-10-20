-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_numeric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:36:03.275993+00:00
-- url     : https://prove2.me/submissions/bbddd67f-bbfd-4c8c-b9a4-67336bb7c9d0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean:L220-L256
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_numeric. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedNonsplit_natRowCount_div_le_width
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedNonsplit_nonsplit_loss_bound_nat

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedNonsplit ----
namespace OAI

/-! Loss counting for nonsplit rows with a local row-pair matching bound. -/

namespace TreeEdit.BinaryLower.TaggedNonsplit

open scoped BigOperators

/-- Numeric nonsplit estimate with exactly the row convention `position/B/m`
and the natural unmatched count. -/
theorem nonsplit_loss_numeric {N T m B : ℕ}
    (u : Fin N → ℕ) (hu : Function.Injective u)
    (hm : 0 < m) (hB : 0 < B) (hub : ∀ i, u i < T * m * B)
    (S : Finset ℕ) (hS : S ⊆ Finset.range T) (d : ℝ)
    (hnonsplit : ∀ r < T, r ∉ S →
      ((Finset.univ.filter fun i => u i / B / m = r).card : ℝ) ≤
        (m * B : ℕ) - d) :
    d * ((T : ℝ) - S.card) ≤ ((T * m * B - N : ℕ) : ℝ) := by
  classical
  have hW : 0 < B * m := Nat.mul_pos hB hm
  have hub' : ∀ i, u i < T * (B * m) := by
    intro i
    simpa only [Nat.mul_comm B m, Nat.mul_assoc] using hub i
  have hrow : ∀ i, u i / B / m < T := by
    intro i
    rw [Nat.div_div_eq_div_mul]
    exact (Nat.div_lt_iff_lt_mul hW).mpr (hub' i)
  have hN : N ≤ T * m * B := by
    calc
      N = (Finset.univ : Finset (Fin N)).card := by simp
      _ ≤ (Finset.range (T * m * B)).card := by
        apply Finset.card_le_card_of_injOn u
        · intro i _
          exact Finset.mem_range.mpr (hub i)
        · exact fun i _ j _ hij => hu hij
      _ = T * m * B := Finset.card_range _
  have h := nonsplit_loss_bound_nat (fun i => u i / B / m) S (m * B : ℕ) d
    hrow hS (fun r _ => ?_) hnonsplit
  · rw [Nat.cast_sub hN]
    simpa only [Nat.cast_mul, mul_assoc] using h
  · have hc := natRowCount_div_le_width u hu (B * m) hW r
    rw [Nat.mul_comm B m] at hc
    simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm B m] using
      (Nat.cast_le.mpr hc : (natRowCount (fun i => u i / (m * B)) r : ℝ) ≤
        ((m * B : ℕ) : ℝ))

end TreeEdit.BinaryLower.TaggedNonsplit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedNonsplit
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_numeric := @_root_.OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_numeric
