-- Prove2me | solution 1 for MetricCodes.MRRW.inverse_zero_fibre_boundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/c5365fd8-aa5c-4713-9ee7-be6a622a9e9c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_spectralLimit_zero_fibre_boundary
import Theorems.Thm_MetricCodes_Johnson_mrrwObjective_zero_fibre_boundary

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
set_option maxHeartbeats 1200000
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ r : ℝ}
    (hδ : 0 < δ) (_ : δ < (1 : ℝ) / 2)
    (hr : 0 < r) (hupper : r < 1 - 2 * δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hrplus : 0 < 1 + r := by linarith
  have hrminus : 0 < 1 - r := by linarith
  have hmargin : 0 < 1 - 2 * δ - r := by linarith
  have hrvariance : 0 < 1 - r ^ 2 := by
    nlinarith only [mul_pos hrminus hrplus]
  have hquadratic :
      0 < 1 - (r ^ 2 + 2 * δ * r + 2 * δ) := by
    nlinarith only [mul_pos hrplus hmargin]
  have hradorder :
      1 - (r ^ 2 + 2 * δ * r + 2 * δ) <
        1 - r ^ 2 := by
    nlinarith only [mul_pos hδ hrplus]
  have hrootorder :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) <
        Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_lt_sqrt hquadratic.le hradorder
  have hrootlt : Real.sqrt (1 - r ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith only [mul_pos hr hr]
  have hsmallroot :
      0 < Real.sqrt
        (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) :=
    Real.sqrt_pos.mpr hquadratic
  have hdegreesquare :
      Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
    Real.sq_sqrt hrvariance.le
  have hweightsquare :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) ^ 2 =
        1 - (r ^ 2 + 2 * δ * r + 2 * δ) :=
    Real.sq_sqrt hquadratic.le
  let u : ℝ := inverseDegree r
  let a : ℝ := inverseWeight δ r
  have hu : 0 < u := by
    dsimp [u, inverseDegree]
    linarith
  have hua : u < a := by
    dsimp [u, a, inverseDegree, inverseWeight]
    linarith
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a, inverseWeight]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have haone : 0 < 1 - a := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvarianceu : 4 * u * (1 - u) = r ^ 2 := by
    dsimp [u, inverseDegree]
    nlinarith only [hdegreesquare]
  have hvariancea :
      4 * a * (1 - a) =
        r ^ 2 + 2 * δ * r + 2 * δ := by
    dsimp [a, inverseWeight]
    nlinarith only [hweightsquare]
  have hdistancevariance : 2 * δ < 4 * a * (1 - a) := by
    rw [hvariancea]
    nlinarith only [mul_pos hδ hr, sq_nonneg r]
  have hvarianceweight : 4 * a * (1 - a) < 4 * a := by
    nlinarith only [mul_pos ha0 ha0]
  have hweightdistance : δ / 2 < a := by
    nlinarith only [hdistancevariance, hvarianceweight]
  have husquare := Real.sq_sqrt (mul_pos hu huone).le
  have hrootsquare :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 = r ^ 2 := by
    nlinarith only [husquare, hvarianceu]
  have huradical :
      2 * Real.sqrt (u * (1 - u)) = r := by
    calc
      2 * Real.sqrt (u * (1 - u)) =
          Real.sqrt ((2 * Real.sqrt (u * (1 - u))) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (r ^ 2) := by rw [hrootsquare]
      _ = r := Real.sqrt_sq hr.le
  have hplus : 1 + r ≠ 0 := hrplus.ne'
  have hfraction :
      (a * (1 - a) - u * (1 - u)) /
        (a * (1 - a) * (1 + r)) =
        δ / (2 * a * (1 - a)) := by
    field_simp [ha0.ne', haone.ne', hplus] ;
      nlinarith only [hvariancea, hvarianceu]
  have hspectral :
      1 - MetricCodes.Johnson.spectralLimit a 0 0 u =
        (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + r)) := by
    simpa only [huradical] using
      MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  have hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a := by
    unfold MetricCodes.Johnson.asymptoticThreshold
    linarith only [hspectral, hfraction]
  have hobjective :
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
    simpa only [huradical] using
      MetricCodes.Johnson.mrrwObjective_zero_fibre_boundary
        hu hua ha hboundary
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hobjective⟩
end MetricCodes.MRRW
