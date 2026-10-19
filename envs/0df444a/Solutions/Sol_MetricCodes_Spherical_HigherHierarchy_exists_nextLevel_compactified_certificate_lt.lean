-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_nextLevel_compactified_certificate_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/0e9a6259-f574-49aa-9a2c-f6500dade51b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Gamma_prepend_scale
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_nextLevel_compactified_certificate_lt_of_spectral_limit

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
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s c R : ℝ}
    (hc : 0 < c) (hc' : c < 1)
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b)
    (hscaled : s < 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hR : Phi a b - Real.logb 2 c < R) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < R :=
  exists_nextLevel_compactified_certificate_lt_of_spectral_limit
    hc hc' a b h hscaled hR (tendsto_Gamma_prepend_scale h hc hc')
end MetricCodes.Spherical.HigherHierarchy
