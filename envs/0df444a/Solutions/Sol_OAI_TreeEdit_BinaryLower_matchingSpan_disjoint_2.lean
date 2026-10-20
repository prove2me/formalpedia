-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.matchingSpan_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:19:15.310924+00:00
-- url     : https://prove2.me/submissions/0df5db5c-7eb3-4d68-a717-49a14fcecb3f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/MatchingSpanBudget.lean:L60-L77
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.matchingSpan_disjoint. The node keeps its source
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

/-- Distinct order-convex label fibers have disjoint interval hulls. -/
theorem matchingSpan_disjoint {r n : ℕ} {β : Type*} [DecidableEq β]
    (f : Fin r → Fin n) (hf : StrictMono f) (label : Fin r → β)
    (hc : ∀ {i j k}, i ≤ j → j ≤ k → label i = label k → label j = label i)
    {b c : β} (hbc : b ≠ c) :
    Disjoint (matchingSpan f label b) (matchingSpan f label c) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨i, j, hi, hj, hip, hpj⟩ := (mem_matchingSpan f label b p).mp hp
  obtain ⟨k, l, hk, hl, hkp, hpl⟩ := (mem_matchingSpan f label c p).mp hq
  rcases le_total i k with hik | hki
  · have hkj : k ≤ j := hf.le_iff_le.mp (hkp.trans hpj)
    have heq := hc hik hkj (hi.trans hj.symm)
    exact hbc (hi.symm.trans (heq.symm.trans hk))
  · have hil : i ≤ l := hf.le_iff_le.mp (hip.trans hpl)
    have heq := hc hki hil (hk.trans hl.symm)
    exact hbc (hi.symm.trans (heq.trans hk))

end
end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_disjoint := @_root_.OAI.TreeEdit.BinaryLower.matchingSpan_disjoint
