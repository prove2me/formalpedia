-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:55:03.189638+00:00
-- url     : https://prove2.me/submissions/132b54dd-95d4-481d-a6fc-7367ecf8ff10

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentMatchingCount.lean:L75-L91
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_RandomMatching_card_segmentMatchingEvent_le

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentMatchingCount ----
namespace OAI

namespace TreeEdit.BinaryLower.RandomMatching

/-- The fixed-window union bound in normalized counting-measure form. -/
theorem segmentMatchingEvent_fraction_le {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) (hs : s ≤ a) :
    ((segmentMatchingEvent s i j u v).card : ℝ) / (2 : ℝ) ^ (K * P) ≤
      ((a.choose s : ℝ) ^ 2) / (2 : ℝ) ^ s := by
  have ha : a ≤ P := by simpa using Fintype.card_le_of_injective v hv
  have hK : 1 ≤ K := by have := i.isLt; omega
  have hsKP : s ≤ K * P := by nlinarith
  have hmul : (segmentMatchingEvent s i j u v).card * 2 ^ s ≤
      (a.choose s) ^ 2 * 2 ^ (K * P) := by
    calc
      _ ≤ ((a.choose s) ^ 2 * 2 ^ (K * P - s)) * 2 ^ s :=
        Nat.mul_le_mul_right _ (card_segmentMatchingEvent_le i j hne u v hv)
      _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hsKP]
  apply (div_le_div_iff₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).2
  exact_mod_cast hmul

end TreeEdit.BinaryLower.RandomMatching

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.RandomMatching


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le := @_root_.OAI.TreeEdit.BinaryLower.RandomMatching.segmentMatchingEvent_fraction_le
