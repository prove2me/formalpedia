-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.Code.eventually_short_pair_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:46:04.687468+00:00
-- url     : https://prove2.me/submissions/1697f511-490e-48ea-918d-9c59f851352d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/CodeNumerics.lean:L16-L40
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.Code.eventually_short_pair_error. The node keeps its source
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

/-- Eventually the error from the short block-pair spans fits within half a block. -/
theorem eventually_short_pair_error :
    ∀ᶠ M : ℕ in atTop,
      0 < M ∧ 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 := by
  have hlog : (fun M : ℕ => Real.logb 2 (M : ℝ)) =o[atTop]
      (fun M : ℕ => (M : ℝ)) :=
    (Real.isLittleO_logb_id_atTop (b := 2)).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hb := hlog.bound (show (0 : ℝ) < 1 / 960 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (8 : ℕ)] with M hM h8
  have hpos : 0 < M := by omega
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast h8
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hlog0 : 0 ≤ Real.logb 2 (M : ℝ) :=
    Real.logb_nonneg (by norm_num) hM1
  have hlogbound : Real.logb 2 (M : ℝ) ≤ (1 / 960 : ℝ) * M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hM0] using hM
  have hceil : (segmentThreshold M : ℝ) < 120 * Real.logb 2 (M : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hsmall : (segmentThreshold M : ℝ) ≤ (M : ℝ) / 4 := by
    linarith
  refine ⟨hpos, ?_⟩
  have := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 2 * (M : ℝ) by positivity)
  nlinarith

end TreeEdit.BinaryLower.Code

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
open Filter Asymptotics


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.Code.eventually_short_pair_error := @_root_.OAI.TreeEdit.BinaryLower.Code.eventually_short_pair_error
