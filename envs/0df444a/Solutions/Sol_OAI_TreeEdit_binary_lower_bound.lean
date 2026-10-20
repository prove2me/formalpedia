-- Prove2me | solution 1 for OAI.TreeEdit.binary_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:32:36.292661+00:00
-- url     : https://prove2.me/submissions/a0b960d0-8c6e-4257-a1b8-28a916fdcafb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/BinaryLowerBound.lean:L10-L22
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TreeEdit.binary_lower_bound.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TreeEdit_binary_lower_bound) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments
import Theorems.Thm_OAI_TreeEdit_BinaryLower_binary_lower_bound_of_finite_source_family
import Theorems.Thm_OAI_TreeEdit_BinaryLower_exists_finite_source_family
import Theorems.Thm_OAI_TreeEdit_BinaryLower_fixed_length_binary_conversion

-- ---- from OAI.Combinatorics.BinaryEdit.BinaryLowerBound ----
namespace OAI

namespace TreeEdit

open BinaryLower

/-- Introduction, `thm:binary`: actual equal-length binary witnesses for every
sufficiently large cap, from the finite-tree family and quadratic block code. -/
theorem binary_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  apply binary_lower_bound_of_finite_source_family ?_ exists_finite_source_family
  obtain ⟨M₀, hcode⟩ := fixed_length_binary_conversion.{0}
  refine ⟨M₀, ?_⟩
  intro M hM Γ inst hΓ1 hΓM
  obtain ⟨c, _, hc⟩ := hcode M hM Γ hΓ1 hΓM
  exact ⟨c, fun x y => (hc x y).1⟩

end TreeEdit

end OAI

-- ---- mission target ----
open OAI OAI.TreeEdit
universe u
open BinaryLower

namespace OAI
namespace TreeEdit
theorem _root_.solution :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  first
    | exact OAI.TreeEdit.binary_lower_bound
    | (apply OAI.TreeEdit.binary_lower_bound <;> assumption)
    | (intros; apply OAI.TreeEdit.binary_lower_bound <;> assumption)
end TreeEdit
end OAI
