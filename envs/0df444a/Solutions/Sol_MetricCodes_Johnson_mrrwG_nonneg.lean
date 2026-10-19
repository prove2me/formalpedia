-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwG_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/19feadf5-50b7-4ad0-bf0b-9232746391fb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_binaryEntropy_nonneg

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ mrrwG v := by
  have hroot : Real.sqrt (1 - v) ≤ 1 :=
    Real.sqrt_le_one.mpr (by linarith)
  have hroot' : 0 ≤ Real.sqrt (1 - v) :=
    Real.sqrt_nonneg _
  unfold mrrwG
  apply MetricCodes.binaryEntropy_nonneg
  · linarith
  · linarith
end MetricCodes.Johnson
