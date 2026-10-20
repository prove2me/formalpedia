-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:13:51.312989+00:00
-- url     : https://prove2.me/submissions/9fe14b95-4e9e-4140-b0d8-735f8cb9be0f

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : Monotone f) (label : Fin r → β)
    (b : β) (hex : ∃ i, label i = b) :
    ∃ i j, label i = b ∧ label j = b ∧ i ≤ j ∧
      matchingSpan f label b = Finset.Icc (f i) (f j) ∧
      (matchingSpan f label b).card = (f j).val + 1 - (f i).val := by
  classical
  set S := Finset.univ.filter fun i => label i = b with hS
  have hne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hex; exact ⟨i, by simp [hS, hi]⟩
  have hmin := Finset.min'_mem S hne
  have hmax := Finset.max'_mem S hne
  simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hmin hmax
  have hspan : matchingSpan f label b = Finset.Icc (f (S.min' hne)) (f (S.max' hne)) := by
    ext p
    rw [mem_matchingSpan, Finset.mem_Icc]
    constructor
    · rintro ⟨i, j, hi, hj, hip, hpj⟩
      have h1 : S.min' hne ≤ i := Finset.min'_le S i (by simp [hS, hi])
      have h2 : j ≤ S.max' hne := Finset.le_max' S j (by simp [hS, hj])
      exact ⟨(hf h1).trans hip, hpj.trans (hf h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨_, _, hmin, hmax, h1, h2⟩
  refine ⟨S.min' hne, S.max' hne, hmin, hmax, Finset.min'_le_max' S hne, hspan, ?_⟩
  rw [hspan, Fin.card_Icc]

