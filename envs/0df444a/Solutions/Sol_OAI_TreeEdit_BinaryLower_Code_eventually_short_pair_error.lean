-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.eventually_short_pair_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:13:39.316807+00:00
-- url     : https://prove2.me/submissions/b3282f6b-973a-4cd5-a05e-4175dc8cbe4d

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


theorem solution :
    ∀ᶠ M : ℕ in atTop,
      0 < M ∧ 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 := by
  have h1 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (1/1000 : ℝ) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have h2 : ∀ᶠ x : ℝ in atTop, (100 : ℝ) ≤ x := eventually_ge_atTop 100
  have h3 := (h1.and h2)
  have h4 := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually h3
  filter_upwards [h4] with M hM
  obtain ⟨hl, hge⟩ := hM
  have hMpos : (0 : ℝ) < M := by linarith
  refine ⟨by exact_mod_cast hMpos, ?_⟩
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hMpos.le] at hl
  have hlog2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlb : Real.logb 2 (M : ℝ) ≤ (M : ℝ) / 690 := by
    rw [Real.logb, div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hc : (segmentThreshold M : ℝ) ≤ 120 * Real.logb 2 (M : ℝ) + 1 := by
    unfold segmentThreshold
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 120 * Real.logb 2 (M : ℝ) by
      have : 0 ≤ Real.logb 2 (M : ℝ) := Real.logb_nonneg (by norm_num) (by linarith)
      linarith)
    linarith
  have hs0 : (0 : ℝ) ≤ segmentThreshold M := by positivity
  nlinarith

