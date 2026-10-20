-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.matchingSpan_inter_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:32:28.815978+00:00
-- url     : https://prove2.me/submissions/aa96c338-4f66-45e4-8669-d23b190a16d8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean:L30-L58
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.matchingSpan_inter_image. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSpanBudget ----
namespace OAI

namespace TreeEdit.BinaryLower

noncomputable section

/-- An order-convex label fiber contains every matched position in its span. -/
theorem matchingSpan_inter_image {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    matchingSpan f label b ∩ Finset.univ.image f =
      (Finset.univ.filter fun i => label i = b).image f := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hspan, himage⟩ := Finset.mem_inter.mp hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp himage
    obtain ⟨i, j, hi, hj, hleft, hright⟩ :=
      (mem_matchingSpan f label b (f k)).mp hspan
    apply Finset.mem_image.mpr
    refine ⟨k, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (hc (hf.le_iff_le.mp hleft) (hf.le_iff_le.mp hright)
      (hi.trans hj.symm)).trans hi
  · intro hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
    have hlabel := (Finset.mem_filter.mp hk).2
    apply Finset.mem_inter.mpr
    constructor
    · exact (mem_matchingSpan f label b (f k)).mpr
        ⟨k, k, hlabel, hlabel, le_rfl, le_rfl⟩
    · exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

end
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_inter_image := @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_inter_image
