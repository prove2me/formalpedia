-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.CodeUnionBound.exists_avoiding_of_sum_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:56:50.397333+00:00
-- url     : https://prove2.me/submissions/1a49a540-0db4-4924-956a-771aa4e505c3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeUnionBound.lean:L15-L34
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.CodeUnionBound.exists_avoiding_of_sum_card_lt. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.CodeUnionBound ----
namespace OAI

/-!
Finite union-bound lemmas for the independent random binary codebook argument
in polynomial-code.tex, Lemma `lem:random-segments`.
-/

namespace TreeEdit.BinaryLower
namespace CodeUnionBound

open scoped BigOperators

/-- A finite family whose total cardinality is smaller than the ambient type
cannot cover that type. No probability-space assumptions are required. -/
theorem exists_avoiding_of_sum_card_lt
    {Ω I : Type*} [Fintype Ω] [Fintype I]
    (bad : I → Finset Ω)
    (h : (∑ i, (bad i).card) < Fintype.card Ω) :
    ∃ ω : Ω, ∀ i : I, ω ∉ bad i := by
  classical
  by_contra hn
  push Not at hn
  have hcover : (Finset.univ : Finset Ω) ⊆ Finset.univ.biUnion bad := by
    intro ω _
    obtain ⟨i, hi⟩ := hn ω
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hc : Fintype.card Ω ≤ ∑ i, (bad i).card := by
    calc
      Fintype.card Ω = (Finset.univ : Finset Ω).card := by simp
      _ ≤ (Finset.univ.biUnion bad).card := Finset.card_le_card hcover
      _ ≤ ∑ i, (bad i).card := Finset.card_biUnion_le
  exact (not_lt_of_ge hc) h

end CodeUnionBound
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.CodeUnionBound
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.CodeUnionBound.exists_avoiding_of_sum_card_lt := @_root_.OAI.TreeEdit.BinaryLower.CodeUnionBound.exists_avoiding_of_sum_card_lt
