-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.card_grid_chain_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:17:33.335329+00:00
-- url     : https://prove2.me/submissions/b9798ab4-f767-4aaf-99ae-f84ed4063955

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/BlockPairCount.lean:L7-L35
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.card_grid_chain_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.BlockPairCount ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- A componentwise chain in a rectangular integer grid has at most
`M + N - 1` points. This counts the block pairs visited by an increasing
subsequence matching; no alignment of block boundaries is assumed. -/
theorem card_grid_chain_le (s : Finset (ℕ × ℕ)) (M N : ℕ)
    (hbound : ∀ p ∈ s, p.1 < M ∧ p.2 < N)
    (hchain : ∀ p ∈ s, ∀ q ∈ s,
      (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2)) :
    s.card ≤ M + N - 1 := by
  let rank : ℕ × ℕ → ℕ := fun p => p.1 + p.2
  have hinj : Set.InjOn rank s := by
    intro p hp q hq heq
    have h := hchain p hp q hq
    dsimp [rank] at heq
    rcases p with ⟨i, j⟩
    rcases q with ⟨i', j'⟩
    have hi : i = i' := by rcases h with h | h <;> omega
    have hj : j = j' := by rcases h with h | h <;> omega
    simp [hi, hj]
  have hsub : s.image rank ⊆ Finset.range (M + N - 1) := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    have hp' := hbound p hp
    simp only [Finset.mem_range]
    dsimp [rank]
    omega
  calc
    s.card = (s.image rank).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.range (M + N - 1)).card := Finset.card_le_card hsub
    _ = M + N - 1 := Finset.card_range _

end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.card_grid_chain_le := @_root_.OAI.TreeEdit.BinaryLower.card_grid_chain_le
