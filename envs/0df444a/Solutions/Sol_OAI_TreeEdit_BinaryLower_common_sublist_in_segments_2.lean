-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.common_sublist_in_segments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:24:35.757157+00:00
-- url     : https://prove2.me/submissions/60827ff7-b8f7-457c-9a8c-a6a24f58e17c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSegments.lean:L89-L119
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.common_sublist_in_segments. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSublist ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Strictly increasing index selections produce sublists. -/
theorem ofFn_get_sublist {α : Type*} (x : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (hi : StrictMono i) :
    (List.ofFn (fun t => x.get (i t))).Sublist x := by
  rw [List.sublist_iff_exists_fin_orderEmbedding_get_eq]
  let f : Fin (List.ofFn (fun t => x.get (i t))).length → Fin x.length :=
    fun t => i ⟨t, by simpa using t.isLt⟩
  have hf : StrictMono f := fun _ _ h => hi h
  refine ⟨OrderEmbedding.ofStrictMono f hf, ?_⟩
  intro t
  simp [f]

/-- A matching described by two increasing index maps is a common sublist
with exactly as many symbols as matched index pairs. -/
theorem common_sublist_of_strict_matching {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t)) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧ z.length = k := by
  refine ⟨List.ofFn (fun t => x.get (i t)), ofFn_get_sublist x i hi, ?_, by simp⟩
  have heq : (fun t => x.get (i t)) = (fun t => y.get (j t)) := funext hlabel
  rw [heq]
  exact ofFn_get_sublist y j hj

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSegments ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Shifting indices into a list segment preserves the selected letter. -/
theorem get_segmentIndex {α : Type*} (x : List α) (start width : ℕ)
    (i : Fin x.length) (hlo : start ≤ (i : ℕ)) (hhi : (i : ℕ) < start + width) :
    ((x.drop start).take width).get (segmentIndex x start width i hlo hhi) =
      x.get i := by
  simp only [List.get_eq_getElem, segmentIndex, List.getElem_take, List.getElem_drop]
  congr 1
  omega

/-- An increasing matching confined to two intervals is a common subsequence
of the corresponding contiguous segments. -/
theorem common_sublist_in_segments {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t))
    (a b p q : ℕ)
    (hi_lo : ∀ t, a ≤ (i t : ℕ)) (hi_hi : ∀ t, (i t : ℕ) < a + p)
    (hj_lo : ∀ t, b ≤ (j t : ℕ)) (hj_hi : ∀ t, (j t : ℕ) < b + q) :
    ∃ z : List α, z.Sublist ((x.drop a).take p) ∧
      z.Sublist ((y.drop b).take q) ∧ z.length = k := by
  let u : Fin k → Fin ((x.drop a).take p).length := fun t =>
    segmentIndex x a p (i t) (hi_lo t) (hi_hi t)
  let v : Fin k → Fin ((y.drop b).take q).length := fun t =>
    segmentIndex y b q (j t) (hj_lo t) (hj_hi t)
  apply common_sublist_of_strict_matching _ _ u v
  · intro s t hst
    have h := hi hst
    have hs := hi_lo s
    have ht := hi_lo t
    change (i s : ℕ) - a < (i t : ℕ) - a
    omega
  · intro s t hst
    have h := hj hst
    have hs := hj_lo s
    have ht := hj_lo t
    change (j s : ℕ) - b < (j t : ℕ) - b
    omega
  · intro t
    exact (get_segmentIndex x a p (i t) (hi_lo t) (hi_hi t)).trans
      ((hlabel t).trans (get_segmentIndex y b q (j t) (hj_lo t) (hj_hi t)).symm)

end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.common_sublist_in_segments := @_root_.OAI.TreeEdit.BinaryLower.common_sublist_in_segments
