-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Parameters.finiteLength_log_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:20:25.299291+00:00
-- url     : https://prove2.me/submissions/9729c445-be1e-4be8-be24-c97cf12fb9b4

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Parameters
theorem h49_fl_log {k : ℕ} (hk : 20 ≤ k) :
    Real.log (finiteLength (k + 1) : ℝ) ≤ 300 * (k : ℝ) ^ 2 * Real.log k := by
  have hk' : (20:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (0:ℝ) < k + 1 := by linarith
  unfold finiteLength
  push_cast
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow]
  have hL : Real.log 20 ≤ Real.log k := Real.log_le_log (by norm_num) hk'
  have hL2 : Real.log ((k:ℝ)+1) ≤ 2 * Real.log k := by
    have : Real.log ((k:ℝ)+1) ≤ Real.log (2 * k) := Real.log_le_log hk1 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    have : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hL0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
  have hl1 : 0 ≤ Real.log ((k:ℝ)+1) := Real.log_nonneg (by linarith)
  push_cast
  have e1 : (3 * ((k:ℝ) + 1)) * (Real.log 20 + Real.log ((k:ℝ)+1) + (20 * ((k:ℝ)+1)) * Real.log ((k:ℝ)+1))
      ≤ (3 * ((k:ℝ) + 1)) * (Real.log k + 2 * Real.log k + (20 * ((k:ℝ)+1)) * (2 * Real.log k)) := by
    gcongr
  have e2 : (3 * ((k:ℝ) + 1)) * (Real.log k + 2 * Real.log k + (20 * ((k:ℝ)+1)) * (2 * Real.log k))
      = (3 * ((k:ℝ) + 1) * (40 * k + 43)) * Real.log k := by ring
  have e3 : 3 * ((k:ℝ) + 1) * (40 * k + 43) ≤ 300 * (k:ℝ)^2 := by nlinarith
  calc _ ≤ _ := e1
    _ = _ := e2
    _ ≤ 300 * (k:ℝ)^2 * Real.log k := mul_le_mul_of_nonneg_right e3 hL0

theorem solution {k : ℕ} (hk : 20 ≤ k) :
    Real.log (finiteLength (k + 1) : ℝ) ≤
      300 * (k : ℝ) ^ 2 * Real.log k := by
  exact h49_fl_log hk

