-- Prove2me | solution 1 for OAI.C0Absorption.theta_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:36:02.217589+00:00
-- url     : https://prove2.me/submissions/573ed6b3-7c65-44bd-ae25-c50577c7277a

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty


theorem solution (J j : ℕ) : Continuous (fun r => theta J r j) := by
  have hbA : ∀ k, Continuous (fun u => boundedAngle J u k) := by
    intro k
    unfold boundedAngle
    split_ifs
    · exact continuous_const
    · exact continuous_const
    · exact (transitionAngle_lipschitz k).continuous
  have hTL : Continuous (fun u => thetaLog J u j) := by
    unfold thetaLog
    have := hbA j; have := hbA (j+1)
    fun_prop
  -- far to the left, the angles are frozen
  set u0 : ℝ := (Finset.range (J+1)).inf' ⟨0, by simp⟩ (fun k => Real.log (rho k) - scheduleH)
  have hfrozen : ∀ u, u ≤ u0 → thetaLog J u j = if j = J then 1 else 0 := by
    intro u hu
    have hA : ∀ k, boundedAngle J u k = if J < k then 0 else Real.pi/2 := by
      intro k
      by_cases hk0 : k = 0
      · subst hk0; simp
      by_cases hkJ : J < k
      · simp [boundedAngle, hk0, hkJ]
      · rw [boundedAngle_inner (by omega) (by omega), if_neg hkJ]
        apply transitionAngle_full
        exact hu.trans (Finset.inf'_le _ (Finset.mem_range.2 (by omega)))
    unfold thetaLog
    rw [hA, hA]
    by_cases hj : j = J
    · subst hj; simp
    · rcases lt_or_gt_of_ne hj with h | h
      · simp [hj, show ¬ J < j by omega, show ¬ J < j + 1 by omega]
      · simp [hj, h, show J < j + 1 by omega]
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_trichotomy r 0 with hr | hr | hr
  · have hev : (fun r => theta J r j) =ᶠ[nhds r] fun _ => if j = J then 1 else 0 := by
      filter_upwards [Iio_mem_nhds hr] with x hx
      simp [theta, (Set.mem_Iio.1 hx).le]
    exact continuousAt_const.congr hev.symm
  · subst hr
    have hev : (fun r => theta J r j) =ᶠ[nhds 0] fun _ => if j = J then 1 else 0 := by
      filter_upwards [Iio_mem_nhds (Real.exp_pos u0)] with x hx
      by_cases h0 : x ≤ 0
      · simp [theta, h0]
      · rw [theta, if_neg h0, hfrozen]
        push_neg at h0
        rw [Real.log_le_iff_le_exp h0]; exact (Set.mem_Iio.1 hx).le
    exact continuousAt_const.congr hev.symm
  · have hev : (fun r => theta J r j) =ᶠ[nhds r] fun r => thetaLog J (Real.log r) j := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      simp [theta, not_le.2 (Set.mem_Ioi.1 hx)]
    exact ((hTL.continuousAt).comp (Real.continuousAt_log hr.ne')).congr hev.symm

