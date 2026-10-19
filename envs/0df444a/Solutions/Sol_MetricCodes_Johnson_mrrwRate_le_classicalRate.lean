-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwRate_le_classicalRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/dcbab0be-9a40-4304-b2a3-73fb9b8a8f10

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwObjective_endpoint
import Theorems.Thm_MetricCodes_Johnson_mrrwRate_le_objective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    mrrwRate δ ≤ MetricCodes.Hamming.classicalRate δ := by
  calc
    mrrwRate δ ≤ mrrwObjective δ (1 - 2 * δ) :=
      mrrwRate_le_objective (by linarith) (le_refl _)
    _ = MetricCodes.Hamming.classicalRate δ :=
      mrrwObjective_endpoint hδ hhalf
end MetricCodes.Johnson
