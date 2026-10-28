-- Prove2me | solution 2 for InventoryControl.rq_optimal_reorder_point
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:54:31.136006+00:00
-- url     : https://prove2.me/submissions/e78a851b-307c-4603-a764-a56b36e514e8

import Mathlib
import Definitions.Def_InventoryControl_rq
import Theorems.Thm_InventoryControl_rq_cost_convex
import Theorems.Thm_InventoryControl_rq_cost_deriv

-- carved verbatim out of submission ed6a239d-3b64-4bd6-b9d3-aeb5fa982c54, lines 477-512

section

open MeasureTheory ProbabilityTheory InventoryControl in
theorem solution (h b1 R Q m s : ℝ) (hh : 0 < h) (hb : 0 < b1) (hQ : 0 < Q)
    (hs : 0 < s) :
    (∀ R' : ℝ, rqCost h b1 R Q m s ≤ rqCost h b1 R' Q m s)
      ↔ rqReadyRate R Q m s = b1 / (h + b1) := by
  have hd : HasDerivAt (fun R => rqCost h b1 R Q m s)
      (-b1 + (h + b1) * rqReadyRate R Q m s) R :=
    InventoryControl.rq_cost_deriv h b1 R Q m s hh hb hQ hs
  have hc : 0 < h + b1 := by linarith
  constructor
  · intro hmin
    have hloc : IsLocalMin (fun R => rqCost h b1 R Q m s) R :=
      Filter.Eventually.of_forall (fun R' => hmin R')
    have h0 := hloc.hasDerivAt_eq_zero hd
    rw [eq_div_iff hc.ne']
    linarith
  · intro hS
    have h0 : -b1 + (h + b1) * rqReadyRate R Q m s = 0 := by
      rw [hS]
      field_simp
      ring
    rw [h0] at hd
    have hconv := InventoryControl.rq_cost_convex h b1 Q m s hh hb hQ hs
    intro R'
    rcases lt_trichotomy R R' with hlt | heq | hgt
    · have hsl := hconv.le_slope_of_hasDerivAt (Set.mem_univ R) (Set.mem_univ R') hlt hd
      rw [slope_def_field] at hsl
      have hpos : 0 < R' - R := by linarith
      have := (le_div_iff₀ hpos).mp hsl
      linarith
    · rw [heq]
    · have hsl := hconv.slope_le_of_hasDerivAt (Set.mem_univ R') (Set.mem_univ R) hgt hd
      rw [slope_def_field] at hsl
      have hpos : 0 < R - R' := by linarith
      have := (div_le_iff₀ hpos).mp hsl
      linarith

end
