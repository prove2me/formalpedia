-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.code_failure_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:12:01.921106+00:00
-- url     : https://prove2.me/submissions/0a92f01b-c850-40ab-ae18-654d540d21f6

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
open Filter Asymptotics


theorem solution {M : ℕ} (hM : 1 ≤ M) :
    (9 / 10 : ℝ) ^ segmentThreshold M * (M : ℝ) ^ 12 ≤ 1 := by
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  set L := Real.logb 2 (M:ℝ) with hLdef
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num) (by exact_mod_cast hM)
  have hT : 120 * L ≤ (segmentThreshold M : ℝ) := by
    unfold segmentThreshold; exact Nat.le_ceil _
  have h1 : (9/10:ℝ) ^ segmentThreshold M ≤ (9/10:ℝ) ^ (120 * L) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hT
  have h2 : (9/10:ℝ) ^ (120 * L) ≤ ((1/2:ℝ)^(12:ℕ)) ^ L := by
    rw [Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow (by positivity) _ hL
    rw [show (120:ℝ) = ((120:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h3 : ((1/2:ℝ)^(12:ℕ)) ^ L * (M:ℝ)^12 = 1 := by
    have hM2 : (2:ℝ) ^ L = M := Real.rpow_logb (by norm_num) (by norm_num) hM0
    rw [one_div, inv_pow, Real.inv_rpow (by positivity), ← Real.rpow_pow_comm (by norm_num), hM2,
      inv_mul_cancel₀]
    positivity
  calc (9/10:ℝ) ^ segmentThreshold M * (M:ℝ)^12 ≤ ((1/2:ℝ)^(12:ℕ)) ^ L * (M:ℝ)^12 := by
        gcongr; exact h1.trans h2
    _ = 1 := h3

