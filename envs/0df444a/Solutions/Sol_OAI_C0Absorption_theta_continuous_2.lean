-- Prove2me | solution 2 for OAI.C0Absorption.theta_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:34:59.302919+00:00
-- url     : https://prove2.me/submissions/f4f0546d-cf2f-4b1f-b1d6-61bf4eba2d32

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Angles.lean:L257-L268
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.theta_continuous. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid
import Definitions.Def_OAI_Analysis_C0Absorption_Weights
import Definitions.Def_OAI_Analysis_C0Absorption_Angles

-- ---- from OAI.Analysis.C0Absorption.Angles ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem boundedAngle_full_of_small {J j : ℕ} (hj : j≤J) {r : ℝ} (hr : 0<r)
    (hle : r≤Real.exp (-scheduleH)*rho J) : boundedAngle J (Real.log r) j=Real.pi/2 := by
  by_cases hz : j=0
  · simp [hz]
  · rw [boundedAngle_inner (by omega) hj]
    exact transitionAngle_full j ((log_radius_lower hr J hle).trans (sub_le_sub_right (log_rho_antitone hj) _))

theorem theta_terminal (J j : ℕ) {r : ℝ} (hr : r ≤ Real.exp (-scheduleH)*rho J) :
    theta J r j=if j=J then 1 else 0 := by
  by_cases h : r≤0
  · simp only [theta,h,↓reduceIte]
  have hp : 0<r := lt_of_not_ge h
  simp only [theta,h,↓reduceIte,thetaLog]
  rcases lt_trichotomy j J with hj|rfl|hj
  · rw [boundedAngle_full_of_small hj.le hp hr,boundedAngle_full_of_small (by omega) hp hr,
      Real.sin_pi_div_two,Real.cos_pi_div_two,ite_eq_right hj.ne]
    ring
  · simp only [boundedAngle_full_of_small le_rfl hp hr,boundedAngle_last,
      Real.sin_pi_div_two,Real.cos_zero,ite_true]
    ring
  · simp only [boundedAngle,show j≠0 by omega,show j+1≠0 by omega,hj,
      show J<j+1 by omega,↓reduceIte,Real.sin_zero,Real.cos_zero,ite_eq_right hj.ne',zero_add,sub_self]

theorem boundedAngle_continuous (J j : ℕ) : Continuous (fun u => boundedAngle J u j) := by
  unfold boundedAngle
  split_ifs
  · exact continuous_const
  · exact continuous_const
  · exact (transitionAngle_lipschitz j).continuous

theorem thetaLog_continuous (J j : ℕ) : Continuous (fun u => thetaLog J u j) :=
  ((Real.continuous_sin.comp (boundedAngle_continuous J j)).add (Real.continuous_cos.comp (boundedAngle_continuous J (j+1)))).sub continuous_const

theorem theta_continuous (J j : ℕ) : Continuous (fun r => theta J r j) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : 0<r
  · apply ((thetaLog_continuous J j).continuousAt.comp (Real.continuousAt_log hr.ne')).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hr] with s hs
    simp only [theta,not_le.mpr hs,↓reduceIte,Function.comp_def]
  · have hR : r<Real.exp (-scheduleH)*rho J := lt_of_le_of_lt (le_of_not_gt hr)
      (mul_pos (Real.exp_pos _) (rho_pos J))
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hR] with s hs
    exact theta_terminal J j hs.le

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution : type_of% @_root_.OAI.C0Absorption.theta_continuous := @_root_.OAI.C0Absorption.theta_continuous
