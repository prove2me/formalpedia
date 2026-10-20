-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:26:17.464901+00:00
-- url     : https://prove2.me/submissions/c7588427-dd8c-439b-9f33-5407a1ab3644

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSegments.lean:L140-L161
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_in_segments

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSegments ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Witness form of the restricted matching-to-segment bound. -/
theorem common_sublist_subset_in_segments {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist ((x.drop a).take p) ∧
      z.Sublist ((y.drop b).take q) ∧ z.length = S.card := by
  let e : Fin S.card ↪o Fin k := S.orderEmbOfFin rfl
  have he (t : Fin S.card) : e t ∈ S := S.orderEmbOfFin_mem rfl t
  apply common_sublist_in_segments x y (i ∘ e) (j ∘ e)
    (hi.comp e.strictMono) (hj.comp e.strictMono) (fun t => hlabel (e t)) a b p q
  · exact fun t => hi_lo (e t) (he t)
  · exact fun t => hi_hi (e t) (he t)
  · exact fun t => hj_lo (e t) (he t)
  · exact fun t => hj_hi (e t) (he t)

/-- Raw fixed-length function interface for the segment witness. -/
theorem common_sublist_subset_ofFn_segments {α : Type*} {n m k : ℕ}
    (x : Fin n → α) (y : Fin m → α)
    (i : Fin k → Fin n) (j : Fin k → Fin m)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x (i t) = y (j t))
    (S : Finset (Fin k)) (a b p q : ℕ)
    (hi_lo : ∀ t ∈ S, a ≤ (i t : ℕ)) (hi_hi : ∀ t ∈ S, (i t : ℕ) < a + p)
    (hj_lo : ∀ t ∈ S, b ≤ (j t : ℕ)) (hj_hi : ∀ t ∈ S, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist (((List.ofFn x).drop a).take p) ∧
      z.Sublist (((List.ofFn y).drop b).take q) ∧ z.length = S.card := by
  let f : Fin k → Fin (List.ofFn x).length :=
    fun t => Fin.cast List.length_ofFn.symm (i t)
  let g : Fin k → Fin (List.ofFn y).length :=
    fun t => Fin.cast List.length_ofFn.symm (j t)
  have hf : StrictMono f := (Fin.cast_strictMono _).comp hi
  have hg : StrictMono g := (Fin.cast_strictMono _).comp hj
  have hmatch : ∀ t, (List.ofFn x).get (f t) = (List.ofFn y).get (g t) := by
    intro t
    simpa [f, g] using hlabel t
  exact common_sublist_subset_in_segments (List.ofFn x) (List.ofFn y)
    f g hf hg hmatch S a b p q hi_lo hi_hi hj_lo hj_hi

end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments := @_root_.OAI.TreeEdit.BinaryLower.common_sublist_subset_ofFn_segments
