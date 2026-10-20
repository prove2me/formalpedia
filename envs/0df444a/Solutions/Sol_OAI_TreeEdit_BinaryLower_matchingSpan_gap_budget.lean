-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.matchingSpan_gap_budget
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:21:18.021619+00:00
-- url     : https://prove2.me/submissions/de6c6d01-c188-4cd6-84ae-53d009beafa0

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
theorem h49_span_disj {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    {b c : β} (hbc : b ≠ c) :
    Disjoint (matchingSpan f label b) (matchingSpan f label c) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  rw [mem_matchingSpan] at hp hq
  obtain ⟨i, j, hi, hj, hip, hpj⟩ := hp
  obtain ⟨i', j', hi', hj', hip', hpj'⟩ := hq
  have h1 : i ≤ j' := hf.le_iff_le.1 (hip.trans hpj')
  have h2 : i' ≤ j := hf.le_iff_le.1 (hip'.trans hpj)
  rcases le_total i i' with h | h
  · have := hc h h2 (hi.trans hj.symm)
    exact hbc (hi.symm.trans (this.symm.trans hi'))
  · have := hc h h1 (hi'.trans hj'.symm)
    exact hbc (hi.symm.trans (this.trans hi'))

theorem solution {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    (s : Finset β) :
    (∑ b ∈ s, ((matchingSpan f label b).card -
      (Finset.univ.filter fun i => label i = b).card)) ≤ n - r := by
  classical
  let G : Finset (Fin n) := Finset.univ \ Finset.univ.image f
  have hG : G.card = n - r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hf.injective, Finset.card_univ, Fintype.card_fin]
  have hterm : ∀ b ∈ s, (matchingSpan f label b).card -
      (Finset.univ.filter fun i => label i = b).card ≤ (matchingSpan f label b ∩ G).card := by
    intro b _
    have hsub : matchingSpan f label b \ G ⊆ (Finset.univ.filter fun i => label i = b).image f := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have : p ∈ Finset.univ.image f := by
        by_contra hh; exact hp2 (by simp [G, hh])
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp this
      rw [mem_matchingSpan] at hp1
      obtain ⟨i0, j0, h0, h1, hle1, hle2⟩ := hp1
      have a1 : i0 ≤ i := hf.le_iff_le.1 hle1
      have a2 : i ≤ j0 := hf.le_iff_le.1 hle2
      have := hc a1 a2 (h0.trans h1.symm)
      exact Finset.mem_image.mpr ⟨i, by simp [this, h0], rfl⟩
    have c1 := Finset.card_le_card hsub
    have c2 := Finset.card_image_le (s := Finset.univ.filter fun i => label i = b) (f := f)
    have c3 := Finset.card_sdiff_add_card_inter (matchingSpan f label b) G
    omega
  calc _ ≤ ∑ b ∈ s, (matchingSpan f label b ∩ G).card := Finset.sum_le_sum hterm
    _ = (s.biUnion fun b => matchingSpan f label b ∩ G).card := by
        rw [Finset.card_biUnion]
        intro b _ c _ hbc
        exact Finset.disjoint_of_subset_left Finset.inter_subset_left
          (Finset.disjoint_of_subset_right Finset.inter_subset_left (h49_span_disj f hf label hc hbc))
    _ ≤ G.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun b _ => Finset.inter_subset_right)
    _ = n - r := hG

