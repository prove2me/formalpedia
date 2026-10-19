-- Prove2me | solution 1 for OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:15:10.334396+00:00
-- url     : https://prove2.me/submissions/fffa5aae-445a-42c4-8dbe-01ef8b387c21

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates

open OAI OAI.Problem356 OAI.Problem356.CoulombEstimates
universe uE uA
open MeasureTheory
open scoped ENNReal
theorem pb_inv_diff {eta a b c : ℝ} (heta : 0 < eta) (ha : eta ≤ a) (hb : eta ≤ b)
    (hab : |a - b| ≤ c) : |a⁻¹ - b⁻¹| ≤ c / eta ^ 2 := by
  have ha0 : 0 < a := lt_of_lt_of_le heta ha
  have hb0 : 0 < b := lt_of_lt_of_le heta hb
  have hc : 0 ≤ c := le_trans (abs_nonneg _) hab
  have e : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
  rw [e, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
  calc |a - b| / (a * b) ≤ c / (a * b) := by gcongr
    _ ≤ c / eta ^ 2 := by
      apply div_le_div_of_nonneg_left hc (by positivity)
      rw [sq]; exact mul_le_mul ha hb heta.le ha0.le

theorem pb_dist_diff {E : Type*} [PseudoMetricSpace E] {x y x' y' : E} {delta : ℝ}
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |dist x y - dist x' y'| ≤ 2 * delta := by
  have := dist_dist_dist_le x y x' y'
  rw [Real.dist_eq] at this
  linarith

theorem solution {E : Type uE} [PseudoMetricSpace E]
    {x y z x' y' z' : E} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    |realCost x y z - realCost x' y' z'| ≤ (6 * delta) / eta ^ 2 := by
  unfold realCost
  have h1 := pb_inv_diff heta hxy hxy' (pb_dist_diff hx hy)
  have h2 := pb_inv_diff heta hxz hxz' (pb_dist_diff hx hz)
  have h3 := pb_inv_diff heta hyz hyz' (pb_dist_diff hy hz)
  have e : (dist x y)⁻¹ + (dist x z)⁻¹ + (dist y z)⁻¹ - ((dist x' y')⁻¹ + (dist x' z')⁻¹ + (dist y' z')⁻¹)
    = ((dist x y)⁻¹ - (dist x' y')⁻¹) + ((dist x z)⁻¹ - (dist x' z')⁻¹) + ((dist y z)⁻¹ - (dist y' z')⁻¹) := by ring
  rw [e]
  calc _ ≤ |(dist x y)⁻¹ - (dist x' y')⁻¹| + |(dist x z)⁻¹ - (dist x' z')⁻¹| + |(dist y z)⁻¹ - (dist y' z')⁻¹| :=
        abs_add_three _ _ _
    _ ≤ 2 * delta / eta ^ 2 + 2 * delta / eta ^ 2 + 2 * delta / eta ^ 2 := by gcongr
    _ = 6 * delta / eta ^ 2 := by ring

