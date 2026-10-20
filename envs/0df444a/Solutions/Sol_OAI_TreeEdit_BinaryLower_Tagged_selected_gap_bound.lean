-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.selected_gap_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:22:55.922809+00:00
-- url     : https://prove2.me/submissions/edb67ddb-4ae1-4b51-b033-86f1a26d787f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedGaps.lean:L23-L45
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.selected_gap_bound. The node keeps its source
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

/-- The sum of the open gaps of an increasing matching telescopes. -/
theorem sum_open_gaps {n : ℕ} (v : Fin (n + 1) → ℕ) :
    (∑ i : Fin n, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1)) =
      (v (Fin.last n) : ℝ) - (v 0 : ℝ) - n := by
  have hs := Fin.sum_univ_succ (fun i : Fin (n + 1) => (v i : ℝ))
  have ht := Fin.sum_univ_castSucc (fun i : Fin (n + 1) => (v i : ℝ))
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  linarith

/-- Chosen disjoint gaps cannot exceed the total number of unmatched target
positions. No assumption about aligned row boundaries is made. -/
theorem selected_gap_bound {n N : ℕ} (v : Fin (n + 1) → ℕ)
    (hv : StrictMono v) (hN : ∀ i, v i < N) (S : Finset (Fin n))
    (g : ℝ) (hg : ∀ i ∈ S, g ≤ (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :
    (S.card : ℝ) * g ≤ (N : ℝ) - (n + 1) := by
  have hpos (i : Fin n) : 0 ≤ (v i.succ : ℝ) - (v i.castSucc : ℝ) - 1 := by
    have h := hv (show i.castSucc < i.succ by simp)
    have hc : (v i.castSucc : ℝ) + 1 ≤ (v i.succ : ℝ) := by exact_mod_cast h
    linarith
  have hsum : (S.card : ℝ) * g ≤
      ∑ i : Fin n, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) := by
    calc
      (S.card : ℝ) * g = ∑ i ∈ S, g := by simp
      _ ≤ ∑ i ∈ S, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :=
        sum_le_sum hg
      _ ≤ ∑ i : Fin n, ((v i.succ : ℝ) - (v i.castSucc : ℝ) - 1) :=
        sum_le_sum_of_subset_of_nonneg (subset_univ S) (by intro i _ _; exact hpos i)
  rw [sum_open_gaps] at hsum
  have hlast : (v (Fin.last n) : ℝ) + 1 ≤ (N : ℝ) := by
    exact_mod_cast hN (Fin.last n)
  have hzero : 0 ≤ (v 0 : ℝ) := Nat.cast_nonneg _
  linarith

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.selected_gap_bound := @_root_.OAI.TreeEdit.BinaryLower.Tagged.selected_gap_bound
