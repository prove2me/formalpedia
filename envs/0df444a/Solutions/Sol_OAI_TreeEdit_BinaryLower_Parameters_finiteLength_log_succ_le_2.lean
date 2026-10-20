-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Parameters.finiteLength_log_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:15:42.738409+00:00
-- url     : https://prove2.me/submissions/798e520e-0b3e-45b2-8103-52f898cc8578

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteParameters.lean:L25-L68
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Parameters.finiteLength_log_succ_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteParameters ----
namespace OAI

namespace TreeEdit.BinaryLower.Parameters

lemma log_finiteLength {k : ℕ} (hk : 0 < k) :
    Real.log (finiteLength k : ℝ) =
      60 * (k : ℝ) ^ 2 * Real.log k + 3 * k * Real.log (20 * k) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold finiteLength
  push_cast
  rw [Real.log_pow, Real.log_mul (by positivity : (20 : ℝ) * k ≠ 0)
    (pow_ne_zero _ hkR), Real.log_pow]
  push_cast
  ring

lemma finiteLength_log_succ_le {k : ℕ} (hk : 20 ≤ k) :
    Real.log (finiteLength (k + 1) : ℝ) ≤
      300 * (k : ℝ) ^ 2 * Real.log k := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hxk : (k : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlogx : Real.log ((k : ℝ) + 1) ≤ 2 * Real.log k := by
    calc
      Real.log ((k : ℝ) + 1) ≤ Real.log ((k : ℝ) ^ 2) :=
        Real.log_le_log hx hxk
      _ = 2 * Real.log k := by rw [Real.log_pow]; norm_num
  have hk2 : (400 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hprod : 20 * ((k : ℝ) + 1) ≤ (k : ℝ) ^ 3 := by
    have := mul_le_mul_of_nonneg_right hk2 (le_of_lt hkpos)
    nlinarith
  have hlogprod : Real.log (20 * ((k : ℝ) + 1)) ≤ 3 * Real.log k := by
    calc
      Real.log (20 * ((k : ℝ) + 1)) ≤ Real.log ((k : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) hprod
      _ = 3 * Real.log k := by rw [Real.log_pow]; norm_num
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := by
    nlinarith
  have hterm1 : 60 * ((k : ℝ) + 1) ^ 2 * Real.log ((k : ℝ) + 1) ≤
      180 * (k : ℝ) ^ 2 * Real.log k := by
    calc
      _ ≤ 60 * ((k : ℝ) + 1) ^ 2 * (2 * Real.log k) :=
        mul_le_mul_of_nonneg_left hlogx (by positivity)
      _ ≤ 60 * ((3 / 2 : ℝ) * (k : ℝ) ^ 2) * (2 * Real.log k) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity)
      _ = _ := by ring
  have hterm2 : 3 * ((k : ℝ) + 1) * Real.log (20 * ((k : ℝ) + 1)) ≤
      18 * (k : ℝ) ^ 2 * Real.log k := by
    calc
      _ ≤ 3 * ((k : ℝ) + 1) * (3 * Real.log k) :=
        mul_le_mul_of_nonneg_left hlogprod (by positivity)
      _ ≤ 18 * (k : ℝ) ^ 2 * Real.log k := by
        have := mul_le_mul_of_nonneg_right hxk hlog
        nlinarith
  rw [log_finiteLength (by omega : 0 < k + 1)]
  push_cast
  nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hlog]

end TreeEdit.BinaryLower.Parameters

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Parameters.finiteLength_log_succ_le := @_root_.OAI.TreeEdit.BinaryLower.Parameters.finiteLength_log_succ_le
