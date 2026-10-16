-- Prove2me | solution 1 for OAI.BoxTransport.Routing.balancedScale_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T13:39:04.974206+00:00
-- url     : https://prove2.me/submissions/91fae4e0-b568-4570-8cd5-9c8da5601bc6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Motion.lean:L310-L327
-- (upload_full_project.md Phase 4): solution for node OAI.BoxTransport.Routing.balancedScale_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion

-- ---- from OAI.Analysis.BoxTransport.Motion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Separated five-stage motions and explicit affine time-one delivery. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
theorem linearBlend_product_lower {s t u : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    min 1 (s * t) ≤ (1 - u + u * s) * (1 - u + u * t) := by
  have hb (s : ℝ) := linearBlend_between (s := s) hu
  have hbs : 0 ≤ 1 - u + u * s := (linearBlend_pos hs hu).le
  have hbt : 0 ≤ 1 - u + u * t := (linearBlend_pos ht hu).le
  by_cases hs' : 1 ≤ s <;> by_cases ht' : 1 ≤ t
  · have h₁ : 1 ≤ 1 - u + u * s := by simpa [min_eq_left hs'] using (hb s).1
    have h₂ : 1 ≤ 1 - u + u * t := by simpa [min_eq_left ht'] using (hb t).1
    exact (min_le_left _ _).trans (by nlinarith)
  · have hc : 0 ≤ u * (1 - u) * (s - 1) * (1 - t) :=
      mul_nonneg (mul_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2))
        (sub_nonneg.mpr hs')) (sub_nonneg.mpr (le_of_not_ge ht'))
    have hl := (linearBlend_between (s := s * t) hu).1
    nlinarith
  · have hc : 0 ≤ u * (1 - u) * (1 - s) * (t - 1) :=
      mul_nonneg (mul_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2))
        (sub_nonneg.mpr (le_of_not_ge hs'))) (sub_nonneg.mpr ht')
    have hl := (linearBlend_between (s := s * t) hu).1
    nlinarith
  · have h₁ : s ≤ 1 - u + u * s := by simpa [min_eq_right (le_of_not_ge hs')] using (hb s).1
    have h₂ : t ≤ 1 - u + u * t := by simpa [min_eq_right (le_of_not_ge ht')] using (hb t).1
    exact (min_le_right _ _).trans (mul_le_mul h₁ h₂ ht.le hbs)

theorem balancedScale_le (s : Space) (hs : ∀ j, 0 < s j)
    (hdet : ∏ j : Fin 3, s j = 1) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (j : Fin 3) :
    balancedScale s u j ≤ max 1 (s j) := by
  fin_cases j
  · exact (linearBlend_between hu).2
  · exact (linearBlend_between hu).2
  have hp := linearBlend_product_lower (hs 0) (hs 1) hu
  have hd : (s 0 * s 1)⁻¹ = s 2 := by
    exact inv_eq_of_mul_eq_one_right (by simpa [Fin.prod_univ_three] using hdet)
  change ((1 - u + u * s 0) * (1 - u + u * s 1))⁻¹ ≤ max 1 (s 2)
  by_cases he : 1 ≤ s 0 * s 1
  · rw [min_eq_left he] at hp
    apply le_trans _ (le_max_left _ _)
    exact inv_le_one_of_one_le₀ hp
  · rw [min_eq_right (le_of_not_ge he)] at hp
    apply le_trans _ (le_max_right _ _)
    rw [← hd]
    exact inv_anti₀ (mul_pos (hs 0) (hs 1)) hp

end BoxTransport.Routing

end

end OAI

-- ---- platform node ----
open OAI OAI.BoxTransport OAI.BoxTransport.Routing
open scoped Topology
open scoped BigOperators ContDiff


theorem solution : type_of% @_root_.OAI.BoxTransport.Routing.balancedScale_le := @_root_.OAI.BoxTransport.Routing.balancedScale_le
