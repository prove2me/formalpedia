-- Prove2me | solution 1 for OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:15:37.541921+00:00
-- url     : https://prove2.me/submissions/bf1b8225-0322-4ad9-9342-934096a9445e

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

theorem pb_abs_realCost {E : Type*} [PseudoMetricSpace E]
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

theorem pb_invDistance {x y : E3} (h : 0 < dist x y) :
    invDistance x y = ENNReal.ofReal (dist x y)⁻¹ := by
  unfold invDistance
  rw [← dist_eq_norm, ENNReal.ofReal_inv_of_pos h]

theorem pb_coulomb_eq {x y z : E3} (h1 : 0 < dist x y) (h2 : 0 < dist x z) (h3 : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold coulombCost realCost tripleFst tripleSnd tripleThd
  simp only
  rw [pb_invDistance h1, pb_invDistance h2, pb_invDistance h3,
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity)]

theorem solution {x y z x' y' z' : E3} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    coulombCost (x, (y, z)) ≤ coulombCost (x', (y', z')) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) := by
  have hd := pb_abs_realCost heta hxy hxz hyz hxy' hxz' hyz' hx hy hz
  rw [pb_coulomb_eq (by linarith) (by linarith) (by linarith),
    pb_coulomb_eq (by linarith) (by linarith) (by linarith)]
  have hnn : 0 ≤ realCost x' y' z' := by unfold realCost; positivity
  have hc : 0 ≤ 6 * delta / eta ^ 2 := le_trans (abs_nonneg _) hd
  rw [← ENNReal.ofReal_add hnn hc]
  apply ENNReal.ofReal_le_ofReal
  have := (abs_le.mp hd).2
  linarith

