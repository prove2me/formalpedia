-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.code_failure_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:47:51.31598+00:00
-- url     : https://prove2.me/submissions/33b7a315-6ad4-449b-aef4-a3aa22d0346f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeNumerics.lean:L104-L144
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.code_failure_power_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.CodeNumerics ----
namespace OAI

/-! Numerical estimates used in the fixed-length binary conversion. -/

open Filter Asymptotics

namespace TreeEdit.BinaryLower.Code

/-- Elementary failure tail at the source logarithmic segment threshold. -/
theorem code_failure_power_bound {M : ℕ} (hM : 1 ≤ M) :
    (9 / 10 : ℝ) ^ segmentThreshold M * (M : ℝ) ^ 12 ≤ 1 := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := by linarith
  have hlog0 := Real.log_nonneg hM1
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hlogbase : Real.log (M : ℝ) ≤ Real.logb 2 (M : ℝ) := by
    rw [Real.logb, le_div_iff₀ hlog2pos]
    nlinarith
  have hthreshold : 120 * Real.log (M : ℝ) ≤ (segmentThreshold M : ℝ) := by
    have hceil := Nat.le_ceil (120 * Real.logb 2 (M : ℝ))
    change 120 * Real.logb 2 (M : ℝ) ≤ (segmentThreshold M : ℝ) at hceil
    linarith
  have hbase : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10 : ℝ)) := by
    have := Real.add_one_le_exp (-(1 / 10 : ℝ))
    linarith
  have htail : (9 / 10 : ℝ) ^ segmentThreshold M ≤
      Real.exp (-(12 * Real.log (M : ℝ))) := by
    calc
      (9 / 10 : ℝ) ^ segmentThreshold M ≤
          Real.exp (-(1 / 10 : ℝ)) ^ segmentThreshold M :=
        pow_le_pow_left₀ (by norm_num) hbase _
      _ = Real.exp ((segmentThreshold M : ℝ) * (-(1 / 10 : ℝ))) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-(12 * Real.log (M : ℝ))) :=
        Real.exp_monotone (by linarith)
  have hexp : Real.exp (-(12 * Real.log (M : ℝ))) = ((M : ℝ) ^ 12)⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    have := Real.exp_nat_mul (Real.log (M : ℝ)) 12
    norm_num only [Nat.cast_ofNat] at this
    rw [this, Real.exp_log hMpos]
  rw [hexp] at htail
  have hmul := mul_le_mul_of_nonneg_right htail
    (show 0 ≤ (M : ℝ) ^ 12 by positivity)
  simpa [ne_of_gt hMpos] using hmul

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
open Filter Asymptotics


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.code_failure_power_bound := @_root_.OAI.TreeEdit.BinaryLower.Code.code_failure_power_bound
