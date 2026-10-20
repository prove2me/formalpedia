-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Parameters.finite_cap_sqrt_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:17:48.923846+00:00
-- url     : https://prove2.me/submissions/2c58b57e-ca77-41be-921c-9de0c1a7e34e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteParameters.lean:L133-L156
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Parameters.finite_cap_sqrt_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Parameters_finiteLength_log_succ_le

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteParameters ----
namespace OAI

namespace TreeEdit.BinaryLower.Parameters

lemma le_finiteLength {k : ℕ} (hk : 0 < k) : k ≤ finiteLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow (by omega : 0 < 3 * k))

lemma finiteLength_log_succ_pos {k : ℕ} (hk : 20 ≤ k) :
    0 < Real.log (finiteLength (k + 1) : ℝ) := by
  apply Real.log_pos
  have := le_finiteLength (by omega : 0 < k + 1)
  exact_mod_cast (show 1 < finiteLength (k + 1) by omega)

lemma finiteLength_loglog_succ_le {k : ℕ} (hk : 20 ≤ k) :
    Real.log (Real.log (finiteLength (k + 1) : ℝ)) ≤
      5 * Real.log k := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hk2 : (300 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hlog : Real.log (k : ℝ) ≤ k := Real.log_le_self hk0
  have hbound : Real.log (finiteLength (k + 1) : ℝ) ≤ (k : ℝ) ^ 5 := by
    calc
      _ ≤ 300 * (k : ℝ) ^ 2 * Real.log k := finiteLength_log_succ_le hk
      _ ≤ 300 * (k : ℝ) ^ 3 := by
        have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 300 * (k : ℝ) ^ 2 by positivity)
        nlinarith
      _ ≤ (k : ℝ) ^ 5 := by
        have := mul_le_mul_of_nonneg_right hk2 (pow_nonneg hk0 3)
        nlinarith
  calc
    _ ≤ Real.log ((k : ℝ) ^ 5) :=
      Real.log_le_log (finiteLength_log_succ_pos hk) hbound
    _ = 5 * Real.log k := by rw [Real.log_pow]; norm_num

/-- The logarithmic scale at any cap below the next construction length. -/
lemma finite_cap_sqrt_bound {k d : ℕ} (hk : 20 ≤ k) (hd : 2 ≤ d)
    (hcap : d ≤ finiteLength (k + 1)) :
    Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤
      40 * k * Real.log k := by
  have hkR : (20 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith only [hkR])
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hdlog : 0 < Real.log (d : ℝ) := Real.log_pos hdR
  have hlogcap : Real.log (d : ℝ) ≤ Real.log (finiteLength (k + 1) : ℝ) :=
    Real.log_le_log (lt_trans zero_lt_one hdR) (Nat.cast_le.mpr hcap)
  have hlogbound : Real.log (d : ℝ) ≤ 300 * (k : ℝ) ^ 2 * Real.log k :=
    hlogcap.trans (finiteLength_log_succ_le hk)
  have hloglogbound : Real.log (Real.log (d : ℝ)) ≤ 5 * Real.log k :=
    (Real.log_le_log hdlog hlogcap).trans (finiteLength_loglog_succ_le hk)
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) hk0) hlogk, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hloglogbound hdlog.le
  have h2 := mul_le_mul_of_nonneg_right hlogbound
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hlogk)
  have h3 : 0 ≤ (k : ℝ) ^ 2 * Real.log k ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith only [h1, h2, h3]

end TreeEdit.BinaryLower.Parameters

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Parameters.finite_cap_sqrt_bound := @_root_.OAI.TreeEdit.BinaryLower.Parameters.finite_cap_sqrt_bound
