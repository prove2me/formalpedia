-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:20:58.700727+00:00
-- url     : https://prove2.me/submissions/7c9db26b-19e1-4f2e-a78a-d348f3f3fb34

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean:L171-L192
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints. The node keeps its source
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

/-- Specifying the first and last entries of a fiber gives its exact interval. -/
theorem matchingSpan_eq_Icc {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : Monotone f) (label : Fin r → β)
    (b : β) (i j : Fin r) (hi : label i = b) (hj : label j = b)
    (hext : ∀ k, label k = b → i ≤ k ∧ k ≤ j) :
    matchingSpan f label b = Finset.Icc (f i) (f j) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨a, c, ha, hc, hap, hpc⟩ := (mem_matchingSpan f label b p).mp hp
    exact Finset.mem_Icc.mpr ⟨(hf (hext a ha).1).trans hap,
      hpc.trans (hf (hext c hc).2)⟩
  · intro hp
    obtain ⟨hip, hpj⟩ := Finset.mem_Icc.mp hp
    exact (mem_matchingSpan f label b p).mpr ⟨i, j, hi, hj, hip, hpj⟩

/-- Every nonempty fiber admits endpoints describing the length of its span. -/
theorem matchingSpan_exists_endpoints {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : Monotone f) (label : Fin r → β)
    (b : β) (hex : ∃ i, label i = b) :
    ∃ i j, label i = b ∧ label j = b ∧ i ≤ j ∧
      matchingSpan f label b = Finset.Icc (f i) (f j) ∧
      (matchingSpan f label b).card = (f j).val + 1 - (f i).val := by
  classical
  let fiber := Finset.univ.filter fun i => label i = b
  have hnon : fiber.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  let i := fiber.min' hnon
  let j := fiber.max' hnon
  have hi : label i = b := (Finset.mem_filter.mp (fiber.min'_mem hnon)).2
  have hj : label j = b := (Finset.mem_filter.mp (fiber.max'_mem hnon)).2
  have hext : ∀ k, label k = b → i ≤ k ∧ k ≤ j := by
    intro k hk
    have hmem : k ∈ fiber := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
    exact ⟨fiber.min'_le k hmem, fiber.le_max' k hmem⟩
  have hspan := matchingSpan_eq_Icc f hf label b i j hi hj hext
  exact ⟨i, j, hi, hj, (hext j hj).1, hspan, by rw [hspan, Fin.card_Icc]⟩

end
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints := @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_exists_endpoints
