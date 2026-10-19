-- Prove2me | solution 1 for OAI.C0Absorption.normalization_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:21:13.403539+00:00
-- url     : https://prove2.me/submissions/6b5ff65e-c412-459a-891c-a279ef577db8

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

open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open Set Filter Topology
open scoped NNReal BigOperators
open Set Filter Topology NormedSpace
open scoped NNReal BigOperators
variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]


theorem solution (x y : E) :
    ‖x‖ * dist (normalize x) (normalize y) ≤ 2 * dist x y := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [NormedSpace.normalize_zero_eq_zero, dist_zero_right, NormedSpace.norm_normalize hx, dist_zero_right]
    have := norm_nonneg x
    linarith
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [dist_eq_norm, dist_eq_norm]
  have key : ‖x‖ • (NormedSpace.normalize x - NormedSpace.normalize y) = (x - y) + (1 - ‖x‖ / ‖y‖) • y := by
    rw [smul_sub, NormedSpace.norm_smul_normalize]
    simp only [NormedSpace.normalize, smul_smul]
    rw [sub_smul, one_smul, div_eq_mul_inv]
    abel
  have h1 : ‖x‖ * ‖NormedSpace.normalize x - NormedSpace.normalize y‖ = ‖(x - y) + (1 - ‖x‖ / ‖y‖) • y‖ := by
    rw [← key, norm_smul, Real.norm_of_nonneg hxn.le]
  rw [h1]
  have h2 : ‖(1 - ‖x‖ / ‖y‖) • y‖ = |‖y‖ - ‖x‖| := by
    rw [norm_smul, Real.norm_eq_abs]
    have : (1 - ‖x‖ / ‖y‖) * ‖y‖ = ‖y‖ - ‖x‖ := by field_simp
    rw [← abs_of_pos hyn, ← abs_mul, abs_of_pos hyn, this]
  have h3 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y
  calc ‖(x - y) + (1 - ‖x‖ / ‖y‖) • y‖ ≤ ‖x - y‖ + ‖(1 - ‖x‖ / ‖y‖) • y‖ := norm_add_le _ _
    _ ≤ 2 * ‖x - y‖ := by rw [h2]; linarith

