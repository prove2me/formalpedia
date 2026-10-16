-- Prove2me | solution 1 for OAI.ShortEgyptian.eventually_log_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:24:04.085005+00:00
-- url     : https://prove2.me/submissions/f1b18785-6444-4a07-a673-4bc45cb714cc

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/MomentAsymptotics.lean:L12-L27
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.eventually_log_pow_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentAsymptotics ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

open Filter Topology Asymptotics

theorem eventually_log_pow_le (C : ℝ) (k : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ S : ℝ in atTop, C * (1+Real.log S)^k ≤ S^eps := by
  have hh := ((isLittleO_log_rpow_rpow_atTop (k:ℝ) heps).tendsto_div_nhds_zero).const_mul (max C 0 * 2^k)
  have hh' : Tendsto (fun S : ℝ => (max C 0*2^k) * ((Real.log S)^k / S^eps)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_zero] using hh
  filter_upwards [hh'.eventually_le_const (by norm_num : (0:ℝ)<1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (0:ℝ)] with S h hh hS
  have hp : 0 < S^eps := Real.rpow_pos_of_pos hS _
  have hbound : max C 0 * 2^k * (Real.log S)^k ≤ S^eps := by
    have h' : (max C 0*2^k*(Real.log S)^k)/S^eps ≤ 1 := by simpa [mul_div_assoc] using h
    exact (div_le_one hp).mp h'
  calc
    C * (1+Real.log S)^k ≤ max C 0 * (1+Real.log S)^k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 0 * (2*Real.log S)^k := by gcongr; linarith
    _ = max C 0 * 2^k * (Real.log S)^k := by rw [mul_pow]; ring
    _ ≤ _ := hbound

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
open Filter Topology Asymptotics


theorem solution : type_of% @_root_.OAI.ShortEgyptian.eventually_log_pow_le := @_root_.OAI.ShortEgyptian.eventually_log_pow_le
