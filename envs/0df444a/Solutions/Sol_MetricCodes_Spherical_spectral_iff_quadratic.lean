-- Prove2me | solution 1 for MetricCodes.Spherical.spectral_iff_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/504864c7-4a1a-4ffb-a118-97fc883d4cdd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Gamma_eq_sub

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution {s a b : ℝ} (ha : 0 < a) :
    s < 2 * MetricCodes.Gamma a b ↔
      b * (1 + b) < boundaryQuadratic s a := by
  have hrad : 0 < a * (1 + a) := mul_pos ha (by linarith)
  have hden : 0 < (1 + 2 * a) * Real.sqrt (a * (1 + a)) :=
    mul_pos (by linarith) (Real.sqrt_pos.2 hrad)
  rw [MetricCodes.Gamma_eq_sub, ← mul_div_assoc, lt_div_iff₀ hden]
  unfold boundaryQuadratic
  constructor <;> intro h <;> nlinarith
end MetricCodes.Spherical
