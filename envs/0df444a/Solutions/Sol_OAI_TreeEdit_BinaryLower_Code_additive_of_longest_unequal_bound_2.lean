-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.additive_of_longest_unequal_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:13:47.753209+00:00
-- url     : https://prove2.me/submissions/e0596b8e-2c0a-4ca3-919a-89f4eff7331e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeAdditive.lean:L66-L108
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.additive_of_longest_unequal_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_equal_label_match_count_le

-- ---- from OAI.Combinatorics.BinaryEdit.CodeNumerics ----
namespace OAI

/-! Numerical estimates used in the fixed-length binary conversion. -/

open Filter Asymptotics

namespace TreeEdit.BinaryLower.Code

/-- The equal-label and unequal-label counts combine into the additive
estimate. All quantities are natural cardinalities, so no rounding is hidden. -/
theorem block_counts_to_additive {M P a₀ L r matched equal unequal δ : ℕ}
    (hpartition : matched = equal + unequal)
    (htotal : matched + δ = M * P)
    (hdeficit : r + L = M)
    (hequal : equal ≤ P * L)
    (hunequal : unequal ≤ 200 * δ + 2 * M * a₀) :
    P * r ≤ 201 * δ + 2 * M * a₀ := by
  nlinarith

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeEqualMatches ----
namespace OAI

/-! Ordered equal-label bit matches can be colored by their ordinal modulo
block width. This avoids the bipartite edge-coloring theorem in the source. -/

namespace TreeEdit.BinaryLower.Code

/-- The same estimate for a selected subset of a larger increasing bit matching.
This is convenient when selecting exactly the equal-label edges. -/
theorem equal_label_subset_card_le {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (s : Finset (Fin N))
    (heq : ∀ i ∈ s, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    s.card ≤ P * lcs x y := by
  let e := s.orderEmbOfFin rfl
  exact equal_label_match_count_le hP x y (f ∘ e) (g ∘ e)
    (hf.comp e.strictMono) (hg.comp e.strictMono)
    (fun i => hfx (e i)) (fun i => hgy (e i))
    (fun i => heq (e i) (s.orderEmbOfFin_mem rfl i))

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeAdditive ----
namespace OAI

/-! The longest encoded matching is partitioned by equality of its
original block labels. Segment separation and the span loss budget bound
the number of unequal-label matches. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- Equal-label coloring and the unequal-label estimate, for actual encoded
words and a matching of their longest-common-subsequence length. -/
theorem additive_of_longest_unequal_bound {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (c : α → Word β P) (x y : List α)
    (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin (lcs (encode c x) (encode c y)) → Fin (M*P))
    (hf : StrictMono f) (hg : StrictMono g)
    (hunequal : (unequalEdges x y hx hy hP f g).card ≤
      200*(M*P-lcs (encode c x) (encode c y))+2*M*a₀) :
    P*deficit M x y ≤ 201*deficit (M*P) (encode c x) (encode c y)+2*M*a₀ := by
  classical
  let r := lcs (encode c x) (encode c y)
  let eqedges : Finset (Fin r) := Finset.univ.filter fun t =>
    originalLetterAtBit x hx hP (f t) = originalLetterAtBit y hy hP (g t)
  have hfx : ∀ t, (f t).val/P < x.length := by
    intro t
    rw [hx]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (f t).isLt
  have hgy : ∀ t, (g t).val/P < y.length := by
    intro t
    rw [hy]
    exact (Nat.div_lt_iff_lt_mul hP).mpr (g t).isLt
  have hequal : eqedges.card ≤ P*lcs x y := by
    apply equal_label_subset_card_le hP x y (fun t => (f t).val) (fun t => (g t).val)
      (Fin.val_strictMono.comp hf) (Fin.val_strictMono.comp hg) hfx hgy eqedges
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hpartition : r = eqedges.card + (unequalEdges x y hx hy hP f g).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r)))
      (p := fun t => originalLetterAtBit x hx hP (f t) =
        originalLetterAtBit y hy hP (g t))
    simpa only [eqedges, unequalEdges, Finset.card_univ, Fintype.card_fin] using h.symm
  have hr : r ≤ M*P := by
    have h := lcs_le_length_left (encode c x) (encode c y)
    simpa only [length_encode, hx] using h
  have hL : lcs x y ≤ M := by simpa only [hx] using lcs_le_length_left x y
  exact block_counts_to_additive hpartition
    (show r+deficit (M*P) (encode c x) (encode c y) = M*P by
      simp only [deficit]; exact Nat.add_sub_of_le hr)
    (show deficit M x y+lcs x y=M by
      simp only [deficit]; exact Nat.sub_add_cancel hL)
    hequal hunequal

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution.{u,v} : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.additive_of_longest_unequal_bound.{u,v} := @_root_.OAI.TreeEdit.BinaryLower.Code.additive_of_longest_unequal_bound.{u,v}
