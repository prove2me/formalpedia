-- Prove2me | solution 2 for OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:13:06.8723+00:00
-- url     : https://prove2.me/submissions/c71a7997-718a-4a81-b19b-aa370327e1d9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombEstimates.lean:L126-L146
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Theorems.Thm_OAI_Problem356_CoulombEstimates_abs_realCost_sub_realCost_le

-- ---- from OAI.Analysis.CoulombTransport.CoulombEstimates ----
namespace OAI

universe uE uA

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.CoulombEstimates

/-- The real formula agrees with the extended-valued cost away from collisions. -/
theorem coulombCost_eq_ofReal_realCost {x y z : E3}
    (hxy : 0 < dist x y) (hxz : 0 < dist x z) (hyz : 0 < dist y z) :
    coulombCost (x, (y, z)) = ENNReal.ofReal (realCost x y z) := by
  unfold realCost
  rw [ENNReal.ofReal_add (add_nonneg (inv_nonneg.mpr dist_nonneg)
        (inv_nonneg.mpr dist_nonneg)) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_add (inv_nonneg.mpr dist_nonneg) (inv_nonneg.mpr dist_nonneg),
    ENNReal.ofReal_inv_of_pos hxy, ENNReal.ofReal_inv_of_pos hxz,
    ENNReal.ofReal_inv_of_pos hyz]
  rfl

/-- One-sided extended-valued oscillation bound, suitable for lower integrals. -/
theorem coulombCost_le_add_of_separated {x y z x' y' z' : E3} {eta delta : ℝ}
    (heta : 0 < eta)
    (hxy : eta ≤ dist x y) (hxz : eta ≤ dist x z) (hyz : eta ≤ dist y z)
    (hxy' : eta ≤ dist x' y') (hxz' : eta ≤ dist x' z') (hyz' : eta ≤ dist y' z')
    (hx : dist x x' ≤ delta) (hy : dist y y' ≤ delta) (hz : dist z z' ≤ delta) :
    coulombCost (x, (y, z)) ≤ coulombCost (x', (y', z')) +
      ENNReal.ofReal ((6 * delta) / eta ^ 2) := by
  have hdelta : 0 ≤ delta := dist_nonneg.trans hx
  have hcost : 0 ≤ realCost x' y' z' := by unfold realCost; positivity
  have herr : 0 ≤ (6 * delta) / eta ^ 2 := by positivity
  have h := (abs_sub_le_iff.mp (abs_realCost_sub_realCost_le heta
    hxy hxz hyz hxy' hxz' hyz' hx hy hz)).1
  have hle : realCost x y z ≤ realCost x' y' z' + (6 * delta) / eta ^ 2 := by
    linarith
  rw [coulombCost_eq_ofReal_realCost (heta.trans_le hxy)
      (heta.trans_le hxz) (heta.trans_le hyz),
    coulombCost_eq_ofReal_realCost (heta.trans_le hxy')
      (heta.trans_le hxz') (heta.trans_le hyz'),
    ← ENNReal.ofReal_add hcost herr]
  exact ENNReal.ofReal_le_ofReal hle

end Problem356.CoulombEstimates

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CoulombEstimates
open MeasureTheory
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated := @_root_.OAI.Problem356.CoulombEstimates.coulombCost_le_add_of_separated
