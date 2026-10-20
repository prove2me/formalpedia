-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.code_union_bound_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:49:46.308957+00:00
-- url     : https://prove2.me/submissions/587c15e8-9832-440e-bf0d-76924e7a5def

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeNumerics.lean:L146-L170
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.code_union_bound_lt_one. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_code_failure_power_bound

-- ---- from OAI.Combinatorics.BinaryEdit.CodeNumerics ----
namespace OAI

/-! Numerical estimates used in the fixed-length binary conversion. -/

open Filter Asymptotics

namespace TreeEdit.BinaryLower.Code

/-- The segment-comparison count times the failure bound is below one. -/
theorem code_union_bound_lt_one {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
      (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  have hx : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hpos : (0 : ℝ) < M := by linarith
  have hsq : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have hpoly : (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 ≤ 8 * (M : ℝ) ^ 8 := by
    calc
      (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 ≤
          (M : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2) ^ 3 := by
        gcongr
        linarith
      _ = 8 * (M : ℝ) ^ 8 := by ring
  have hfour : (8 : ℝ) < (M : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num) hx 4
    norm_num at h
    linarith
  have hpoly' : (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 < (M : ℝ) ^ 12 := by
    apply hpoly.trans_lt
    have h := mul_lt_mul_of_pos_right hfour (show (0 : ℝ) < (M : ℝ) ^ 8 by positivity)
    convert h using 1; ring
  have hmul := mul_lt_mul_of_pos_right hpoly'
    (show (0 : ℝ) < (9 / 10 : ℝ) ^ segmentThreshold M by positivity)
  exact hmul.trans_le (by simpa [mul_comm] using code_failure_power_bound (by omega : 1 ≤ M))

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
open Filter Asymptotics


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.code_union_bound_lt_one := @_root_.OAI.TreeEdit.BinaryLower.Code.code_union_bound_lt_one
