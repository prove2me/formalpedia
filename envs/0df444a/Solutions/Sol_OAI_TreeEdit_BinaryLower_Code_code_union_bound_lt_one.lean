-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.code_union_bound_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:13:48.860868+00:00
-- url     : https://prove2.me/submissions/a0e04e51-e189-488c-babb-da73c3dcda52

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


theorem solution {M : ℕ} (hM : 2 ≤ M) :
    (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
      (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  have hM2 : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hM1 : (1:ℝ) ≤ M := by linarith
  set t := Real.logb 2 (M:ℝ) with ht
  have ht0 : 0 ≤ t := Real.logb_nonneg (by norm_num) hM1
  set L := segmentThreshold M with hLdef
  have hL : 120 * t ≤ (L:ℝ) := by
    rw [hLdef, segmentThreshold]; exact Nat.le_ceil _
  set q : ℝ := (9/10:ℝ)^L with hq
  have hq0 : 0 ≤ q := by positivity
  have hqle : q ≤ ((9/10:ℝ)^(120:ℕ))^t := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
    push_cast; linarith
  have hM17 : (M:ℝ)^(17:ℕ) = ((2:ℝ)^(17:ℕ))^t := by
    have : (M:ℝ) = (2:ℝ)^t := by rw [ht, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    conv_lhs => rw [this]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
  have hkey : q * (M:ℝ)^(17:ℕ) ≤ 1 := by
    rw [hM17]
    calc q * ((2:ℝ)^(17:ℕ))^t ≤ ((9/10:ℝ)^(120:ℕ))^t * ((2:ℝ)^(17:ℕ))^t :=
          mul_le_mul_of_nonneg_right hqle (by positivity)
      _ = ((9/10:ℝ)^(120:ℕ) * (2:ℝ)^(17:ℕ))^t := (Real.mul_rpow (by positivity) (by positivity)).symm
      _ ≤ 1 := Real.rpow_le_one (by positivity) (by norm_num) ht0
  have h1 : (M:ℝ)^2 * ((M:ℝ)^2+1)^3 ≤ 8 * (M:ℝ)^8 := by
    have : (M:ℝ)^2 + 1 ≤ 2 * (M:ℝ)^2 := by nlinarith
    calc (M:ℝ)^2 * ((M:ℝ)^2+1)^3 ≤ (M:ℝ)^2 * (2*(M:ℝ)^2)^3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) this 3) (by positivity)
      _ = 8 * (M:ℝ)^8 := by ring
  have h2 : 512 * (M:ℝ)^8 ≤ (M:ℝ)^(17:ℕ) := by
    have : (2:ℝ)^9 ≤ (M:ℝ)^9 := pow_le_pow_left₀ (by norm_num) hM2 9
    have h8 : 0 ≤ (M:ℝ)^8 := by positivity
    calc 512 * (M:ℝ)^8 = (2:ℝ)^9 * (M:ℝ)^8 := by norm_num
      _ ≤ (M:ℝ)^9 * (M:ℝ)^8 := mul_le_mul_of_nonneg_right this h8
      _ = (M:ℝ)^(17:ℕ) := by ring
  have h3 := mul_le_mul_of_nonneg_right h1 hq0
  have h4 := mul_le_mul_of_nonneg_right h2 hq0
  nlinarith

