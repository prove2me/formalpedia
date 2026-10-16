-- Prove2me | solution 1 for OAI.ShortEgyptian.uniform_divisor_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:28:44.014808+00:00
-- url     : https://prove2.me/submissions/bb67c9cb-83f0-4df1-94da-908d52aac61f

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/MomentAsymptotics.lean:L247-L268
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.uniform_divisor_moment. The node keeps its source
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
import Theorems.Thm_OAI_ShortEgyptian_divisor_moment_numeric
import Theorems.Thm_OAI_ShortEgyptian_eventually_log_pow_le

-- ---- from OAI.NumberTheory.ShortEgyptian.MomentAsymptotics ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

open Filter Topology Asymptotics

theorem eventually_nested_log_le (C E : ℝ) (hE : 0 < E) :
    ∀ᶠ S : ℝ in atTop, C*(1+Real.log (E*Real.log S)) ≤ Real.log S := by
  have hh := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hC := (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop).const_div_atTop (1+Real.log E)
  have hlim : Tendsto (fun x : ℝ => C*((1+Real.log E)/x+Real.log x/x)) atTop (𝓝 0) := by
    simpa using (hC.add hh).const_mul C
  have hh' := (hlim.comp Real.tendsto_log_atTop).eventually_le_const (by norm_num : (0:ℝ)<1)
  filter_upwards [hh',Real.tendsto_log_atTop.eventually_gt_atTop 0] with S h hl
  rw [Real.log_mul hE.ne' hl.ne']
  have heq : C * (1+Real.log E+Real.log (Real.log S))/Real.log S =
      C*((1+Real.log E)/Real.log S+Real.log (Real.log S)/Real.log S) := by ring
  change C*((1+Real.log E)/Real.log S+Real.log (Real.log S)/Real.log S) ≤ 1 at h
  have h' := (div_le_one hl).mp (heq.symm ▸ h)
  linarith

theorem uniform_divisor_moment (D : ℝ) (hD : 1 ≤ D) (r : ℕ) :
    ∀ᶠ S : ℝ in atTop, ∀ (v Y : ℝ) (N : ℕ),
      S/(2*Real.log S) ≤ v → v ≤ D*S → Real.exp (v/2) ≤ Y → Y ≤ Real.exp v →
      (N:ℝ) ≤ Real.exp (D*S) →
      ∑ n ∈ Ioc N (N+⌊Y⌋₊), (truncatedDivisorCount (Real.exp v) n:ℝ)^r ≤ Y*Real.exp (S^(1/4:ℝ)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop D,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (1+(D+1)/Real.log 2)),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (1+2/Real.log 2)),
    eventually_log_pow_le 40 1 (by norm_num : (0:ℝ)<1/16),
    eventually_log_pow_le (1600*(r:ℝ)) 2 (by norm_num : (0:ℝ)<1/2),
    eventually_log_pow_le (400*(momentSeriesConst 0*smallSmoothConst)) 1 (by norm_num : (0:ℝ)<1/2),
    eventually_log_pow_le (51200*momentSeriesConst r) 0 (by norm_num : (0:ℝ)<1/20),
    eventually_nested_log_le (3200*(r:ℝ)) (2*(D+1)) (by linarith),
    eventually_nested_log_le 1 (2*(D+1)) (by linarith),
    eventually_log_pow_le (8*(r:ℝ)*D) 1 (by norm_num : (0:ℝ)<1/8),
    eventually_log_pow_le (128*momentSeriesConst r) 1 (by norm_num : (0:ℝ)<1/4),
    eventually_log_pow_le 4 1 (by norm_num : (0:ℝ)<1/4)]
    with S hS hl hDS hElog h2log h40 hp hs hb hB hB1 hbig hpr hout
  simp only [pow_zero,pow_one,mul_one,one_mul] at h40 hs hb hB1 hbig hpr hout
  intro v Y N hvlo hvup hYlo hYup hN
  exact divisor_moment_numeric r D S v Y N hD hS hl hDS hElog h2log h40 hp hs hb hB hB1 hbig hpr hout hvlo hvup hYlo hYup hN

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
open Filter Topology Asymptotics


theorem solution : type_of% @_root_.OAI.ShortEgyptian.uniform_divisor_moment := @_root_.OAI.ShortEgyptian.uniform_divisor_moment
