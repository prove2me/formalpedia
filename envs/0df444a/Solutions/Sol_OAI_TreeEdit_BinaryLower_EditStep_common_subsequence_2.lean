-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.EditStep.common_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:40:08.318446+00:00
-- url     : https://prove2.me/submissions/eb394452-5411-4108-9afc-4928e40da4b5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/EditLCSLower.lean:L9-L31
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.EditStep.common_subsequence. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.EditLCSLower ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Every elementary edit preserves a common subsequence after at most two
unmatched symbols in total. This includes substitutions by the same letter. -/
theorem EditStep.common_subsequence {α : Type*} {x y : List α}
    (h : EditStep x y) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧
      x.length + y.length ≤ 2 + 2 * z.length := by
  cases h with
  | insert p s a =>
      refine ⟨p ++ s, List.Sublist.refl _, ?_, ?_⟩
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons a)
      · simp only [List.length_append, List.length_cons]
        omega
  | delete p s a =>
      refine ⟨p ++ s, ?_, List.Sublist.refl _, ?_⟩
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons a)
      · simp only [List.length_append, List.length_cons]
        omega
  | substitute p s a b =>
      refine ⟨p ++ s, ?_, ?_, ?_⟩
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons a)
      · exact (List.Sublist.refl p).append ((List.Sublist.refl s).cons b)
      · simp only [List.length_append, List.length_cons]
        omega

end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.EditStep.common_subsequence := @_root_.OAI.TreeEdit.BinaryLower.EditStep.common_subsequence
