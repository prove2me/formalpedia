-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwObjective_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/ab50465d-58f6-45f6-a8a4-8d11ff2ba473

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwG_continuous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution (δ : ℝ) :
    Continuous (mrrwObjective δ) := by
  have hsquare : Continuous (fun r : ℝ => r ^ 2) :=
    continuous_id.pow 2
  have hargument :
      Continuous (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ) :=
    (hsquare.add (continuous_const.mul continuous_id)).add
      continuous_const
  unfold mrrwObjective
  exact (continuous_const.add (mrrwG_continuous.comp hsquare)).sub
    (mrrwG_continuous.comp hargument)
end MetricCodes.Johnson
