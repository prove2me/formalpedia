-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Tagged.tagged_slice_alignment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T18:46:23.259561+00:00
-- url     : https://prove2.me/submissions/aa000e66-06fa-4a0f-bfe3-3b36b42004b3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/TaggedAlignment.lean:L56-L105
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Tagged.tagged_slice_alignment. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_BlockRestriction_card_le_lcs_slices
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Tagged_numeric_alignment_bound

-- ---- from OAI.Combinatorics.BinaryEdit.BlockRestriction ----
namespace OAI

/-! Restricting increasing common matchings to arbitrary contiguous intervals. -/

namespace TreeEdit.BinaryLower
namespace BlockRestriction

universe u
variable {α : Type u}

/-- The quotient convention in the tagged-row proof identifies a contiguous
interval of width `m * B`; the order `p / B / m` is retained literally. -/
lemma row_bounds {p m B r : ℕ} (hm : 0 < m) (hB : 0 < B)
    (hrow : p / B / m = r) :
    r * (m * B) ≤ p ∧ p < r * (m * B) + m * B := by
  have hp : p / (m * B) = r := by
    simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm B m] using hrow
  have hbounds := (Nat.div_eq_iff (Nat.mul_pos hm hB)).mp hp
  have hpos := Nat.mul_pos hm hB
  omega

/-- The exact row-pair restriction used in ordered-tag matching arguments.
No row-boundary alignment of the original matching is assumed. -/
theorem card_filter_rows_le_lcs (x y : List α) {n : ℕ}
    (u v : Fin n → ℕ) (hu : StrictMono u) (hv : StrictMono v)
    (hxu : ∀ t, u t < x.length) (hyv : ∀ t, v t < y.length)
    (heq : ∀ t, x[u t]'(hxu t) = y[v t]'(hyv t))
    (m B a b : ℕ) (hm : 0 < m) (hB : 0 < B) :
    (Finset.univ.filter (fun t => u t / B / m = a ∧ v t / B / m = b)).card ≤
      lcs ((x.drop (a * (m * B))).take (m * B))
        ((y.drop (b * (m * B))).take (m * B)) := by
  apply card_le_lcs_slices x y u v hu hv hxu hyv heq
  · intro t ht
    have hrow := ((Finset.mem_filter.mp ht).2).1
    exact row_bounds hm hB hrow
  · intro t ht
    have hrow := ((Finset.mem_filter.mp ht).2).2
    exact row_bounds hm hB hrow

end BlockRestriction
end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.TreeEdit.Alignments ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TreeEdit

universe u

variable {α : Type u} {x y z : List α}

namespace Alignment

variable {n : ℕ}

end Alignment

theorem exists_lcs_alignment (x y : List α) : Nonempty (Alignment x y (lcs x y)) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g, hg⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  refine ⟨⟨(Fin.castOrderIso hz.symm).toOrderEmbedding.comp f,
    (Fin.castOrderIso hz.symm).toOrderEmbedding.comp g, ?_⟩⟩
  intro i
  exact (hf (Fin.cast hz.symm i)).symm.trans (hg (Fin.cast hz.symm i))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.TaggedAlignment ----
namespace OAI

/-! The numeric and list-slice forms of the ordered-tag alignment lemma.
These statements allow arbitrary increasing matchings across row boundaries. -/

namespace TreeEdit.BinaryLower.Tagged

open Finset

/-- Core list version: local row-pair LCS loss and ordered disjoint tags imply
the global harmonic lower bound. Slices are literal contiguous rows of width
`m * B`, and all intermediate subsequence matchings remain unrestricted. -/
theorem tagged_slice_alignment {α : Type*} {T m B : ℕ}
    (hT : 0 < T) (hm : 2 ≤ m) (hB : 0 < B)
    (x y : List α) (hx : x.length = T * m * B) (hy : y.length = T * m * B)
    (htags : ∀ p (hp : p < x.length) q (hq : q < y.length),
      x[p]'hp = y[q]'hq → p / B % m = q / B % m)
    (d : ℝ) (hd : 0 ≤ d)
    (hlocal : ∀ a < T, ∀ b < T,
      (lcs ((x.drop (a * (m * B))).take (m * B))
        ((y.drop (b * (m * B))).take (m * B)) : ℝ) ≤ (m * B : ℕ) - d) :
    (T : ℝ) * d * (((m - 1) * B : ℕ) : ℝ) /
        (d + (((m - 1) * B : ℕ) : ℝ)) ≤
      (deficit (T * m * B) x y : ℝ) := by
  have hmpos : 0 < m := by omega
  have hdW : d ≤ (m * B : ℕ) := by
    have h := hlocal 0 hT 0 hT
    have hnonneg : 0 ≤ (lcs ((x.drop (0 * (m * B))).take (m * B))
        ((y.drop (0 * (m * B))).take (m * B)) : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨⟨f, g, hmatch⟩⟩ := exists_lcs_alignment x y
  let u : Fin (lcs x y) → ℕ := fun i => (f i).val
  let v : Fin (lcs x y) → ℕ := fun i => (g i).val
  have hu : StrictMono u := by
    intro i j hij
    exact f.strictMono hij
  have hv : StrictMono v := by
    intro i j hij
    exact g.strictMono hij
  have hxu : ∀ i, u i < x.length := fun i => (f i).isLt
  have hyv : ∀ i, v i < y.length := fun i => (g i).isLt
  have hub : ∀ i, u i < T * m * B := by simpa only [hx] using hxu
  have hvb : ∀ i, v i < T * m * B := by simpa only [hy] using hyv
  have heq : ∀ i, x[u i]'(hxu i) = y[v i]'(hyv i) := by
    intro i
    simpa only [u, v, List.get_eq_getElem] using hmatch i
  have htagmatch : ∀ i, u i / B % m = v i / B % m := by
    intro i
    exact htags _ (hxu i) _ (hyv i) (heq i)
  have hlocalmatch : ∀ a < T, ∀ b < T,
      ((univ.filter fun i : Fin (lcs x y) =>
        u i / B / m = a ∧ v i / B / m = b).card : ℝ) ≤ (m * B : ℕ) - d := by
    intro a ha b hb
    have h := BlockRestriction.card_filter_rows_le_lcs x y u v hu hv hxu hyv heq
      m B a b hmpos hB
    exact (Nat.cast_le.mpr h).trans (hlocal a ha b hb)
  have h := numeric_alignment_bound hm hB u v hu hv hub hvb htagmatch d hd hdW hlocalmatch
  have hlcs : lcs x y ≤ T * m * B := by simpa only [hx] using lcs_le_length_left x y
  simpa only [deficit, Nat.cast_sub hlcs] using h

end TreeEdit.BinaryLower.Tagged

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Tagged
open Finset


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Tagged.tagged_slice_alignment := @_root_.OAI.TreeEdit.BinaryLower.Tagged.tagged_slice_alignment
