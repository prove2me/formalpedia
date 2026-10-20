-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.equal_match_count_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:10:09.542077+00:00
-- url     : https://prove2.me/submissions/1df8e12c-b5b4-4cee-a092-945a969f6bae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeEqualMatches.lean:L12-L35
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.equal_match_count_le. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_div_strict_of_equal_residue

-- ---- from OAI.Combinatorics.BinaryEdit.CodeEqualMatches ----
namespace OAI

/-! Ordered equal-label bit matches can be colored by their ordinal modulo
block width. This avoids the bipartite edge-coloring theorem in the source. -/

namespace TreeEdit.BinaryLower.Code

/-- If every increasing block matching has at most `L` edges, then an increasing
bit matching whose edges all join equal original labels has at most `P * L`
edges. The hypothesis on each finite subset is precisely the longest-common-
subsequence bound after the two block maps become strictly increasing. -/
theorem equal_match_count_le {N P L : ℕ} (hP : 0 < P)
    (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hL : ∀ s : Finset (Fin N),
      StrictMonoOn (fun i => f i / P) (s : Set (Fin N)) →
      StrictMonoOn (fun i => g i / P) (s : Set (Fin N)) → s.card ≤ L) :
    N ≤ P * L := by
  classical
  have bound := Finset.card_le_mul_card_image_of_maps_to
    (s := Finset.univ) (t := Finset.range P) (f := fun i : Fin N => i.val % P)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i.val hP)) L
    (by
      intro r hr
      apply hL
      · intro i hi j hj hij
        exact div_strict_of_equal_residue hP f hf hij
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
      · intro i hi j hj hij
        exact div_strict_of_equal_residue hP g hg hij
          ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm))
  simpa [Nat.mul_comm] using bound

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.equal_match_count_le := @_root_.OAI.TreeEdit.BinaryLower.Code.equal_match_count_le
