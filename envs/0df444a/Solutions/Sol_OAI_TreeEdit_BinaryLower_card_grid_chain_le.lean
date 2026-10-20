-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.card_grid_chain_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:10:43.944641+00:00
-- url     : https://prove2.me/submissions/08231384-0c57-4173-96e7-584911d0b7bf

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution (s : Finset (ℕ × ℕ)) (M N : ℕ)
    (hbound : ∀ p ∈ s, p.1 < M ∧ p.2 < N)
    (hchain : ∀ p ∈ s, ∀ q ∈ s,
      (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∨ (q.1 ≤ p.1 ∧ q.2 ≤ p.2)) :
    s.card ≤ M + N - 1 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp
  have hM := (hbound p0 hp0).1
  have hN := (hbound p0 hp0).2
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) s := by
    intro p hp q hq hpq
    simp only at hpq
    rcases hchain p hp q hq with h | h
    · exact Prod.ext (by omega) (by omega)
    · exact Prod.ext (by omega) (by omega)
  have hsub : s.image (fun p : ℕ × ℕ => p.1 + p.2) ⊆ Finset.range (M + N - 1) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    have := hbound p hp
    simp only [Finset.mem_range]
    omega
  rw [← Finset.card_image_of_injOn hinj]
  simpa using Finset.card_le_card hsub

