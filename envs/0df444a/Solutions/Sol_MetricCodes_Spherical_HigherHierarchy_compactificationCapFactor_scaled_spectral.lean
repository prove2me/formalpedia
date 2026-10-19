-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactificationCapFactor_scaled_spectral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/03765d28-7823-4128-a207-eb90a4c25fed

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactificationCapFactor_sq

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s t : ℝ}
    (hs : s < 1) (hts : t ≤ s)
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (hgap : t < 2 * Gamma a b) :
    s < 1 - compactificationCapFactor s t ^ 2 *
      (1 - 2 * Gamma a b) := by
  have hden : 0 < 1 - t := by linarith
  rw [compactificationCapFactor_sq hs hts]
  have hrewrite :
      1 - (1 - s) / (1 - t) * (1 - 2 * Gamma a b) =
        (1 - t - (1 - s) * (1 - 2 * Gamma a b)) /
          (1 - t) := by
    field_simp [hden.ne']
  rw [hrewrite]
  apply (lt_div_iff₀ hden).2
  nlinarith [mul_pos (sub_pos.mpr hs) (sub_pos.mpr hgap)]
end MetricCodes.Spherical.HigherHierarchy
