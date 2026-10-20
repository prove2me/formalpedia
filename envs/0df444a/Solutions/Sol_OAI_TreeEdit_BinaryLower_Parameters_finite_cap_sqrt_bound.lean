-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Parameters.finite_cap_sqrt_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:23:01.176543+00:00
-- url     : https://prove2.me/submissions/06923f83-f2b4-4491-98ad-19be23bd1787

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

theorem solution {k d : ℕ} (hk : 20 ≤ k) (hd : 2 ≤ d)
    (hcap : d ≤ finiteLength (k + 1)) :
    Real.sqrt (Real.log (d : ℝ) * Real.log (Real.log (d : ℝ))) ≤
      40 * k * Real.log k := by
  have hk' : (20:ℝ) ≤ k := by exact_mod_cast hk
  have hL0 : 0 < Real.log k := Real.log_pos (by linarith)
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = 300 * (k:ℝ)^2 * Real.log k := ⟨_, rfl⟩
  have hd' : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hld : Real.log d ≤ Λ := by
    have hc : (d:ℝ) ≤ (finiteLength (k+1) : ℝ) := Nat.cast_le.2 hcap
    have : Real.log (d:ℝ) ≤ Real.log (finiteLength (k+1) : ℝ) :=
      Real.log_le_log (by linarith) hc
    exact this.trans (hΛ ▸ h49_fl_log hk)
  clear hcap
  have hld0 : 0 < Real.log d := Real.log_pos (by linarith)
  have hLam : 0 < Λ := by rw [hΛ]; positivity
  -- log Λ ≤ 5 log k
  have hlogΛ : Real.log Λ ≤ 5 * Real.log k := by
    rw [hΛ, Real.log_mul (by positivity) hL0.ne', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have h300 : Real.log 300 ≤ 2 * Real.log k := by
      have : Real.log 300 ≤ Real.log ((k:ℝ)^2) := Real.log_le_log (by norm_num) (by nlinarith [hk'])
      rw [Real.log_pow] at this; push_cast at this; exact this
    have hll : Real.log (Real.log k) ≤ Real.log k := by
      have := Real.log_le_sub_one_of_pos hL0; linarith
    push_cast
    linarith
  have hprod : Real.log d * Real.log (Real.log d) ≤ (40 * k * Real.log k)^2 := by
    rcases le_or_gt (Real.log (Real.log d)) 0 with h | h
    · have : Real.log d * Real.log (Real.log d) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hld0.le h
      nlinarith [sq_nonneg (40 * k * Real.log k)]
    · have h1 : Real.log (Real.log d) ≤ Real.log Λ := Real.log_le_log hld0 hld
      calc Real.log d * Real.log (Real.log d) ≤ Λ * Real.log Λ := by gcongr
        _ ≤ Λ * (5 * Real.log k) := by gcongr
        _ ≤ (40 * k * Real.log k)^2 := by rw [hΛ]; nlinarith [sq_nonneg (k * Real.log k)]
  calc Real.sqrt (Real.log d * Real.log (Real.log d)) ≤ Real.sqrt ((40 * k * Real.log k)^2) :=
        Real.sqrt_le_sqrt hprod
    _ = 40 * k * Real.log k := Real.sqrt_sq (by positivity)

