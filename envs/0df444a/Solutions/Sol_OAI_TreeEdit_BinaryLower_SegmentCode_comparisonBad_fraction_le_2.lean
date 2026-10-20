-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:01:16.35972+00:00
-- url     : https://prove2.me/submissions/e58a22ce-cf63-4e4c-8671-2a2468516865

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentCode.lean:L50-L78
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_RandomMatching_segmentMatchingEvent_fraction_le
import Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_nearly_full_matching_bound

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentCode ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite probabilistic construction of a codebook simultaneously separating every
long segment of every pair of differently labelled blocks. Counting is done on
all Boolean codebooks, so no randomness or existence hypothesis is retained.
-/

namespace TreeEdit.BinaryLower.SegmentCode

open RandomMatching CodeUnionBound

theorem window_injective {P : ℕ} (a i : ℕ) (h : i+a ≤ P) :
    Function.Injective (window a i h) := by
  intro t u he
  apply Fin.ext
  have he' := congrArg Fin.val he
  dsimp [window] at he'
  omega

/-- Each valid comparison has exponentially small bad-event frequency. -/
theorem comparisonBad_fraction_le {K P : ℕ} (a₀ : ℕ)
    (t : SegmentComparison K (P+1)) :
    ((comparisonBad a₀ t).card : ℝ) / Fintype.card (Fin K → Fin P → Bool) ≤
      (9/10 : ℝ)^a₀ := by
  classical
  rcases t with ⟨k, l, a, i, j⟩
  dsimp only [comparisonBad]
  split_ifs with h
  · have hc : Fintype.card (Fin K → Fin P → Bool) = 2^(K*P) := by
      simp [← pow_mul, Nat.mul_comm]
    rw [hc]
    push_cast
    have hs : a.val-a.val/100 ≤ a.val := Nat.sub_le _ _
    have hlarge : 99*a.val ≤ 100*(a.val-a.val/100) := by omega
    have hbin := nearly_full_matching_bound a.val (a.val-a.val/100) hs hlarge
    have hbin' : ((a.val.choose (a.val-a.val/100) : ℝ)^2) /
        (2 : ℝ)^(a.val-a.val/100) ≤ (9/10 : ℝ)^a.val := by
      simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using hbin
    calc
      _ ≤ ((a.val.choose (a.val-a.val/100) : ℝ)^2) /
          (2 : ℝ)^(a.val-a.val/100) :=
        segmentMatchingEvent_fraction_le k l h.1 _ _
          (window_injective _ _ _) hs
      _ ≤ (9/10 : ℝ)^a.val := hbin'
      _ ≤ (9/10 : ℝ)^a₀ := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h.2.1
  · simp only [Finset.card_empty, Nat.cast_zero, zero_div]
    positivity

end TreeEdit.BinaryLower.SegmentCode

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.SegmentCode
open RandomMatching CodeUnionBound


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le := @_root_.OAI.TreeEdit.BinaryLower.SegmentCode.comparisonBad_fraction_le
