-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.numeric_alignment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:41:53.597536+00:00
-- url     : https://prove2.me/submissions/49816200-5165-44ff-98e0-94380debd4e3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedAlignment.lean:L15-L54
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.numeric_alignment_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TaggedNonsplit_nonsplit_loss_numeric
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_nonsplit_row_card_le
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_split_rows_gap_bound

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedGaps ----
namespace OAI

/-! Gap accounting for split rows in ordered-tag alignments. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- Row indices of positions in a `T`-row word are strictly below `T`. -/
theorem row_index_lt {p T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hp : p < T * m * B) : p / B / m < T := by
  apply (Nat.div_lt_iff_lt_mul hm).2
  apply (Nat.div_lt_iff_lt_mul hB).2
  exact hp

theorem splitRows_subset_range {n T m B : ℕ} (hm : 0 < m) (hB : 0 < B)
    (u v : Fin (n + 1) → ℕ) (hu : ∀ i, u i < T * m * B) :
    splitRows m B u v ⊆ range T := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := mem_image.mp hr
  exact mem_range.mpr (row_index_lt hm hB (hu i.castSucc))

/-- The algebraic conclusion of the split and nonsplit accounts, including
zero local deficit. -/
theorem harmonic_bound {E d g T s : ℝ} (hd : 0 ≤ d) (hg : 0 < g)
    (hunsplit : d * (T - s) ≤ E) (hsplit : s * g ≤ E) :
    T * d * g / (d + g) ≤ E := by
  have hden : 0 < d + g := by linarith
  apply (div_le_iff₀ hden).2
  have h1 := mul_le_mul_of_nonneg_left hunsplit (le_of_lt hg)
  have h2 := mul_le_mul_of_nonneg_left hsplit hd
  nlinarith

/-- Empty matchings satisfy the same bound, using only the evident local
upper bound on the row deficit. -/
theorem harmonic_le_total {T d g W : ℝ} (hT : 0 ≤ T) (hd : 0 ≤ d)
    (hg : 0 < g) (hdW : d ≤ W) :
    T * d * g / (d + g) ≤ T * W := by
  have hden : 0 < d + g := by linarith
  calc
    T * d * g / (d + g) ≤ T * d := by
      apply (div_le_iff₀ hden).2
      have hnonneg := mul_nonneg hT (sq_nonneg d)
      nlinarith
    _ ≤ T * W := mul_le_mul_of_nonneg_left hdW hT

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedAlignment ----
namespace OAI

/-! The numeric and list-slice forms of the ordered-tag alignment lemma.
These statements allow arbitrary increasing matchings across row boundaries. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- Complete ordered-tag accounting for an arbitrary increasing matching.
The local bound counts matches in a whole source/target row pair. -/
theorem numeric_alignment_bound {L T m B : ℕ} (hm : 2 ≤ m) (hB : 0 < B)
    (u v : Fin L → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hub : ∀ i, u i < T * m * B) (hvb : ∀ i, v i < T * m * B)
    (htags : ∀ i, u i / B % m = v i / B % m)
    (d : ℝ) (hd : 0 ≤ d) (hdW : d ≤ (m * B : ℕ))
    (hlocal : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin L =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ)) ≤
      (T * m * B : ℕ) - (L : ℝ) := by
  have hmpos : 0 < m := by omega
  have hg : 0 < (((m - 1) * B : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (show 0 < m - 1 by omega) hB
  have hL : L ≤ T * m * B := by
    calc
      L = (univ : Finset (Fin L)).card := by simp
      _ ≤ (range (T * m * B)).card := by
        apply card_le_card_of_injOn u
        · intro i _
          exact mem_range.mpr (hub i)
        · intro i _ j _ hij
          exact hu.injective hij
      _ = T * m * B := card_range _
  cases L with
  | zero =>
      have h := harmonic_le_total (Nat.cast_nonneg T) hd hg hdW
      simpa only [Nat.cast_zero, sub_zero, Nat.cast_mul, mul_assoc] using h
  | succ n =>
      have hnonsplit := TaggedNonsplit.nonsplit_loss_numeric u hu.injective hmpos hB hub
        (splitRows m B u v) (splitRows_subset_range hmpos hB u v hub) d
        (fun a ha haS => nonsplit_row_card_le hmpos hB u v hu.monotone hvb d hdW
          hlocal ha haS)
      rw [Nat.cast_sub hL] at hnonsplit
      simp only [Nat.cast_add, Nat.cast_one] at hnonsplit
      have hsplit := split_rows_gap_bound (by omega) hB u v hu hv hvb htags
      have h := harmonic_bound hd hg hnonsplit hsplit
      simpa only [Nat.cast_add, Nat.cast_one, Nat.succ_eq_add_one] using h

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.numeric_alignment_bound := @_root_.OAI.TreeEdit.BinaryLower.Tagged.numeric_alignment_bound
