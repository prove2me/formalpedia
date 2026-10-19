-- Prove2me | solution 2 for OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:11:29.401429+00:00
-- url     : https://prove2.me/submissions/e140ab3e-143f-4832-9fae-1ed08fd30883

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombEstimates.lean:L71-L96
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates

-- ---- from OAI.Analysis.CoulombTransport.CoulombEstimates ----
namespace OAI

universe uE uA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- The reciprocal is uniformly Lipschitz away from zero. -/
theorem abs_inv_sub_inv_le {a b eta L : ℝ}
    (heta : 0 < eta) (ha : eta ≤ a) (hb : eta ≤ b)
    (hL : |a - b| ≤ L) :
    |a⁻¹ - b⁻¹| ≤ L / eta ^ 2 := by
  have ha0 : 0 < a := heta.trans_le ha
  have hb0 : 0 < b := heta.trans_le hb
  have hL0 : 0 ≤ L := (abs_nonneg _).trans hL
  have hab : eta ^ 2 ≤ a * b := by
    nlinarith [mul_le_mul ha hb (le_of_lt heta) (le_of_lt ha0)]
  have heq : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
  exact (div_le_div_of_nonneg_right hL (le_of_lt (mul_pos ha0 hb0))).trans
    (div_le_div_of_nonneg_left hL0 (sq_pos_of_pos heta) hab)

/-- Moving both endpoints by at most `delta` changes distance by at most `2 * delta`. -/
theorem abs_dist_sub_dist_le {E : Type uE} [PseudoMetricSpace E]
    {x y x' y' : E} {delta : ℝ}
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |dist x y - dist x' y'| ≤ 2 * delta := by
  have h := abs_dist_sub_le x x' y
  have h' := abs_dist_sub_le y y' x'
  calc
    |dist x y - dist x' y'| ≤
        |dist x y - dist x' y| + |dist x' y - dist x' y'| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (dist x y - dist x' y) (dist x' y - dist x' y')
    _ ≤ dist x x' + dist y y' := by
      exact add_le_add h (by simpa only [dist_comm] using h')
    _ ≤ 2 * delta := by linarith

/-- Coulomb pair interaction has a quantitative oscillation estimate on separated products. -/
theorem abs_inv_dist_sub_inv_dist_le {E : Type uE} [PseudoMetricSpace E]
    {x y x' y' : E} {eta delta : ℝ}
    (heta : 0 < eta) (hxy : eta ≤ dist x y) (hxy' : eta ≤ dist x' y')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) :
    |(dist x y)⁻¹ - (dist x' y')⁻¹| ≤ (2 * delta) / eta ^ 2 :=
  abs_inv_sub_inv_le heta hxy hxy' (abs_dist_sub_dist_le hx hy)

/-- Oscillation of the three-particle Coulomb cost on separated, small cells. -/
theorem abs_realCost_sub_realCost_le {E : Type uE} [PseudoMetricSpace E]
    {x y z x' y' z' : E} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    |realCost x y z - realCost x' y' z'| ≤ (6 * delta) / eta ^ 2 := by
  have h1 := abs_inv_dist_sub_inv_dist_le heta hxy hxy' hx hy
  have h2 := abs_inv_dist_sub_inv_dist_le heta hxz hxz' hx hz
  have h3 := abs_inv_dist_sub_inv_dist_le heta hyz hyz' hy hz
  have habs : |realCost x y z - realCost x' y' z'| ≤
      |(dist x y)⁻¹ - (dist x' y')⁻¹| +
      |(dist x z)⁻¹ - (dist x' z')⁻¹| +
      |(dist y z)⁻¹ - (dist y' z')⁻¹| := by
    unfold realCost
    calc
      _ = |((dist x y)⁻¹ - (dist x' y')⁻¹) +
          ((dist x z)⁻¹ - (dist x' z')⁻¹) +
          ((dist y z)⁻¹ - (dist y' z')⁻¹)| := by congr 1; ring
      _ ≤ _ := abs_add_three _ _ _
  calc
    _ ≤ _ := habs
    _ ≤ (2 * delta) / eta ^ 2 + (2 * delta) / eta ^ 2 +
        (2 * delta) / eta ^ 2 := add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

end Problem356.CoulombEstimates

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CoulombEstimates
open MeasureTheory
open scoped ENNReal


theorem solution.{uE} : type_of% @_root_.OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le.{uE} := @_root_.OAI.Problem356.CoulombEstimates.abs_realCost_sub_realCost_le.{uE}
