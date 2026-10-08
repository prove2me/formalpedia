-- Prove2me | solution 1 for HryniewiczCriterion.strictly_convex_isDynamicallyConvex
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T21:16:13.109289+00:00
-- url     : https://prove2.me/submissions/3390b968-1f75-4dcf-886e-c805c57387d3

import Theorems.Thm_HryniewiczCriterion_linearizedXiPath_isSymplecticPath
import Theorems.Thm_HryniewiczCriterion_winding_endpoint_profile
import Theorems.Thm_HryniewiczCriterion_strictly_convex_windingInterval_gt_one
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open HryniewiczCriterion

/-- If the winding interval `[a, b]` satisfies `1 < a ≤ b`, then the index formula of
`czIndexOfPath` is at least `3`. -/
theorem solution (H : R4 → ℝ)
    (hS : IsStrictlyStarShapedLevel H) (hC : IsStrictlyConvexLevel H) :
    IsDynamicallyConvex H := by
  intro P Y hY
  obtain ⟨hφ, hdet, h0⟩ := linearizedXiPath_isSymplecticPath H hS P Y hY
  obtain ⟨Δ, hΔ, hI, -, -⟩ := winding_endpoint_profile _ hφ hdet h0
  have hgt := strictly_convex_windingInterval_gt_one H hS hC P Y hY
  set I := windingInterval (linearizedXiPath H P Y) with hIdef
  have hK : IsCompact I := by
    rw [hI]; exact isCompact_Icc.image hΔ
  have hne : I.Nonempty := by
    rw [hI]; exact ⟨Δ 0, 0, ⟨le_rfl, by positivity⟩, rfl⟩
  have ha : 1 < sInf I := hgt _ (hK.sInf_mem hne)
  have hab : sInf I ≤ sSup I := csInf_le_csSup hne hK.bddBelow hK.bddAbove
  have hb : 1 < sSup I := lt_of_lt_of_le ha hab
  have hceil : (1 : ℤ) < ⌈sSup I⌉ := Int.lt_ceil.mpr (by exact_mod_cast hb)
  show 3 ≤ (if sInf I ≤ ((⌈sSup I⌉ - 1 : ℤ) : ℝ) then 2 * (⌈sSup I⌉ - 1)
    else 2 * ⌈sSup I⌉ - 1)
  split_ifs with h
  · have h1 : (1 : ℝ) < ((⌈sSup I⌉ - 1 : ℤ) : ℝ) := lt_of_lt_of_le ha h
    have h2 : (1 : ℤ) < ⌈sSup I⌉ - 1 := by exact_mod_cast h1
    omega
  · omega
