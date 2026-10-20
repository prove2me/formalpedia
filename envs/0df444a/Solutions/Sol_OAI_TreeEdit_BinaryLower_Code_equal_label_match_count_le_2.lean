-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:11:51.028142+00:00
-- url     : https://prove2.me/submissions/72b3f829-d960-4071-9fbf-fe45651cbfec

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeEqualMatches.lean:L37-L58
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_equal_match_count_le

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

/-- Every increasing matching has size at most the longest common subsequence. -/
theorem matching_length_le_lcs {α : Type*} (x y : List α) {k : ℕ}
    (i : Fin k → Fin x.length) (j : Fin k → Fin y.length)
    (hi : StrictMono i) (hj : StrictMono j)
    (hlabel : ∀ t, x.get (i t) = y.get (j t)) : k ≤ lcs x y := by
  obtain ⟨z, hzx, hzy, hz⟩ := common_sublist_of_strict_matching x y i j hi hj hlabel
  rw [← hz]
  exact length_le_lcs hzx hzy

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeEqualMatches ----
namespace OAI

/-! Ordered equal-label bit matches can be colored by their ordinal modulo
block width. This avoids the bipartite edge-coloring theorem in the source. -/

namespace TreeEdit.BinaryLower.Code

/-- Concrete equal-label case of the modular coloring estimate. The strictly
increasing lists `f,g` are the bit positions of the equal-label matches; their
quotients index the original words. -/
theorem equal_label_match_count_le {α : Type*} {N P : ℕ} (hP : 0 < P)
    (x y : List α) (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hfx : ∀ i, f i / P < x.length) (hgy : ∀ i, g i / P < y.length)
    (heq : ∀ i, x.get ⟨f i / P, hfx i⟩ = y.get ⟨g i / P, hgy i⟩) :
    N ≤ P * lcs x y := by
  apply equal_match_count_le hP f g hf hg
  intro s hs₁ hs₂
  let e := s.orderEmbOfFin rfl
  let f' : Fin s.card → Fin x.length := fun i => ⟨f (e i) / P, hfx (e i)⟩
  let g' : Fin s.card → Fin y.length := fun i => ⟨g (e i) / P, hgy (e i)⟩
  have hf' : StrictMono f' := by
    intro i j hij
    exact hs₁ (s.orderEmbOfFin_mem rfl i) (s.orderEmbOfFin_mem rfl j)
      (e.strictMono hij)
  have hg' : StrictMono g' := by
    intro i j hij
    exact hs₂ (s.orderEmbOfFin_mem rfl i) (s.orderEmbOfFin_mem rfl j)
      (e.strictMono hij)
  exact matching_length_le_lcs x y f' g' hf' hg' (fun i => heq (e i))

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le := @_root_.OAI.TreeEdit.BinaryLower.Code.equal_label_match_count_le
