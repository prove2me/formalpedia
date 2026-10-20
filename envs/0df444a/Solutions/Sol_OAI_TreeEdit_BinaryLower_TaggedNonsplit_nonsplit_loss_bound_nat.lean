-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_bound_nat
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:33:01.259423+00:00
-- url     : https://prove2.me/submissions/4e494353-2d64-4df3-be4c-cb712220d162

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedNonsplit.lean:L159-L195
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_bound_nat. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedNonsplit ----
namespace OAI

/-! Loss counting for nonsplit rows with a local row-pair matching bound. -/

namespace TreeEdit.BinaryLower.TaggedNonsplit

open scoped BigOperators

/-- Partition the matching by natural row indices in `[0,T)`. -/
theorem sum_natRowCount {N T : ℕ} (row : Fin N → ℕ)
    (hrow : ∀ i, row i < T) :
    ∑ r ∈ Finset.range T, natRowCount row r = N := by
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin N)) (Finset.range T) row
  simpa only [natRowCount, Finset.mem_range, hrow, Finset.filter_true,
    Finset.card_univ, Fintype.card_fin] using h

/-- Nonsplit summation with natural row indices, avoiding any conversion of
`splitRows` to a Fin-indexed set. -/
theorem nonsplit_loss_bound_nat {N T : ℕ} (row : Fin N → ℕ)
    (S : Finset ℕ) (W d : ℝ)
    (hrow : ∀ i, row i < T) (hS : S ⊆ Finset.range T)
    (hcapacity : ∀ r < T, (natRowCount row r : ℝ) ≤ W)
    (hnonsplit : ∀ r < T, r ∉ S → (natRowCount row r : ℝ) ≤ W - d) :
    d * ((T : ℝ) - S.card) ≤ (T : ℝ) * W - N := by
  classical
  let G := Finset.range T \ S
  have hsum : (∑ r ∈ Finset.range T, (natRowCount row r : ℝ)) = (N : ℝ) := by
    exact_mod_cast sum_natRowCount row hrow
  have hcard : (G.card : ℝ) = (T : ℝ) - S.card := by
    dsimp [G]
    rw [Finset.card_sdiff_of_subset hS, Finset.card_range, Nat.cast_sub]
    simpa using Finset.card_le_card hS
  have hlow : (G.card : ℝ) * d ≤
      ∑ r ∈ G, (W - (natRowCount row r : ℝ)) := by
    calc
      (G.card : ℝ) * d = ∑ _r ∈ G, d := by simp
      _ ≤ ∑ r ∈ G, (W - (natRowCount row r : ℝ)) := by
        apply Finset.sum_le_sum
        intro r hr
        obtain ⟨hrT, hrS⟩ := Finset.mem_sdiff.mp hr
        have h := hnonsplit r (Finset.mem_range.mp hrT) hrS
        linarith
  have hle : (∑ r ∈ G, (W - (natRowCount row r : ℝ))) ≤
      ∑ r ∈ Finset.range T, (W - (natRowCount row r : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro r hr _
    exact sub_nonneg.mpr (hcapacity r (Finset.mem_range.mp hr))
  have htotal : (∑ r ∈ Finset.range T, (W - (natRowCount row r : ℝ))) =
      (T : ℝ) * W - N := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [hcard] at hlow
  simpa only [mul_comm] using hlow.trans (hle.trans_eq htotal)

end TreeEdit.BinaryLower.TaggedNonsplit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.TaggedNonsplit
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_bound_nat := @_root_.OAI.TreeEdit.BinaryLower.TaggedNonsplit.nonsplit_loss_bound_nat
