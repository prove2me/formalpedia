-- Prove2me | solution 1 for MetricCodes.Spherical.MaximalCodeBounds.exists_sphericalCode_card_eq_number_toNat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/062974bc-7765-465d-90f5-450d80ca08d7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_exists_maximal_sphericalCode
import Theorems.Thm_SpherePacking_exists_maximal_sphericalCode

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open MetricCodes.Spherical.MaximalCodeBounds
namespace MetricCodes.Spherical.MaximalCodeBounds
theorem _root_.solution
    {n : ℕ} {s : ℝ} (hs : s < 1) :
    ∃ C : SpherePacking.SphericalCode n s,
      C.points.card = (SpherePacking.sphericalCodeNumber n s).toNat := by
  obtain ⟨C, hC⟩ := SpherePacking.exists_maximal_sphericalCode hs
  refine ⟨C, ?_⟩
  simpa using congrArg ENat.toNat hC
end MetricCodes.Spherical.MaximalCodeBounds
