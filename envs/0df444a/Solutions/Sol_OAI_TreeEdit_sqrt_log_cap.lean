-- Prove2me | solution 1 for OAI.TreeEdit.sqrt_log_cap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:29:20.345991+00:00
-- url     : https://prove2.me/submissions/1d477b51-35dc-45b0-ad4c-f63f14c1092c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CapInversion.lean:L11-L54
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.sqrt_log_cap. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleFourier
import Definitions.Def_OAI_Combinatorics_TreeEdit_SampledSpectrum
import Definitions.Def_OAI_Combinatorics_TreeEdit_PrimeSupply
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleObstruction
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleParameters
import Definitions.Def_OAI_Combinatorics_TreeEdit_Delimiter
import Definitions.Def_OAI_Combinatorics_TreeEdit_DistortionTransfer

-- ---- from OAI.Combinatorics.TreeEdit.CapInversion ----
namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

lemma sqrt_log_cap {A k d : ℝ} (hA : 1 ≤ A) (hk : 8 * A ≤ k) (hd : 1 < d)
    (hcap : Real.log d ≤ A * (k + 1) ^ 2 * Real.log (k + 1)) :
    Real.sqrt (Real.log d * Real.log (Real.log d)) ≤ 8 * A * (k * Real.log k) := by
  have hk2 : 2 ≤ k := by linarith
  have hkp : 0 < k := by linarith
  have hAp : 0 < A := by linarith
  have hlogk : 0 < Real.log k := Real.log_pos (by linarith)
  have hlogd : 0 < Real.log d := Real.log_pos hd
  have hlk : Real.log (k + 1) ≤ 2 * Real.log k := by
    calc
      _ ≤ Real.log (2 * k) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log k := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hk2]
  have hlk0 : 0 ≤ Real.log (k + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log d ≤ 8 * A * k ^ 2 * Real.log k := by
    calc
      _ ≤ A * (k + 1) ^ 2 * Real.log (k + 1) := hcap
      _ ≤ A * (2 * k) ^ 2 * (2 * Real.log k) := by gcongr; linarith
      _ = _ := by ring
  have hll : Real.log (Real.log d) ≤ 4 * Real.log k := by
    calc
      _ ≤ Real.log (8 * A * k ^ 2 * Real.log k) := Real.log_le_log hlogd hL
      _ = Real.log (8 * A) + 2 * Real.log k + Real.log (Real.log k) := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow]
        ring
      _ ≤ Real.log k + 2 * Real.log k + Real.log k := by
        have ha := Real.log_le_log (by positivity : (0 : ℝ) < 8 * A) hk
        have hb := Real.log_le_log hlogk (show Real.log k ≤ k from by linarith [Real.log_le_sub_one_of_pos hkp])
        linarith
      _ = _ := by ring
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have hh : Real.log d * Real.log (Real.log d) ≤
        (8 * A * k ^ 2 * Real.log k) * (4 * Real.log k) := by
      exact (mul_le_mul_of_nonneg_left hll hlogd.le).trans
        (mul_le_mul_of_nonneg_right hL (by positivity))
    have hAA : 32 * A ≤ (8 * A) ^ 2 := by nlinarith
    calc
      _ ≤ _ := hh
      _ = (32 * A) * (k * Real.log k) ^ 2 := by ring
      _ ≤ (8 * A) ^ 2 * (k * Real.log k) ^ 2 := mul_le_mul_of_nonneg_right hAA (sq_nonneg _)
      _ = _ := by ring

end TreeEdit

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.TreeEdit.sqrt_log_cap := @_root_.OAI.TreeEdit.sqrt_log_cap
