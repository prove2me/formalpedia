-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.matchingSpan_gap_budget
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:34:11.089912+00:00
-- url     : https://prove2.me/submissions/ef215a93-43f8-4c93-a456-166a289b0260

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean:L91-L123
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.matchingSpan_gap_budget. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_disjoint
import Theorems.Thm_OAI_TreeEdit_BinaryLower_matchingSpan_inter_image

-- ---- from OAI.Combinatorics.BinaryEdit.MatchingSpanBudget ----
namespace OAI

namespace TreeEdit.BinaryLower

noncomputable section

/-- The number of unmatched positions in a span is its length minus the
number of matching entries in the corresponding fiber. -/
theorem matchingSpan_unmatched_card {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (b : β) :
    (matchingSpan f label b \ Finset.univ.image f).card =
      (matchingSpan f label b).card - (Finset.univ.filter fun i => label i = b).card := by
  classical
  rw [Finset.card_sdiff, Finset.inter_comm, matchingSpan_inter_image f hf label hc]
  rw [Finset.card_image_of_injective _ hf.injective]

/-- All span gaps together use at most the global number of unmatched
positions. This holds for any selected collection of label fibers. -/
theorem matchingSpan_gap_budget {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (s : Finset β) :
    (∑ b ∈ s, ((matchingSpan f label b).card -
      (Finset.univ.filter fun i => label i = b).card)) ≤ n - r := by
  classical
  let gaps : β → Finset (Fin n) := fun b =>
    matchingSpan f label b \ Finset.univ.image f
  have hdisj : (↑s : Set β).PairwiseDisjoint gaps := by
    intro b hb c hc' hbc
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp (matchingSpan_disjoint f hf label hc hbc))
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1
  have hsub : s.biUnion gaps ⊆ Finset.univ \ Finset.univ.image f := by
    intro p hp
    obtain ⟨b, hb, hpb⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hpb).2⟩
  calc
    (∑ b ∈ s, ((matchingSpan f label b).card -
        (Finset.univ.filter fun i => label i = b).card)) = ∑ b ∈ s, (gaps b).card := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (matchingSpan_unmatched_card f hf label hc b).symm
    _ = (s.biUnion gaps).card := (Finset.card_biUnion hdisj).symm
    _ ≤ (Finset.univ \ Finset.univ.image f).card := Finset.card_le_card hsub
    _ = n - r := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      rw [Finset.card_image_of_injective _ hf.injective]
      simp

end
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_gap_budget := @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_gap_budget
