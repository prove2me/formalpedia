-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_nextLevel_compactified_certificate_lt_of_spectral_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/17496456-9f6d-4939-92a7-acbdd86d1941

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_interlacing_prepend_scale
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_Phi_prepend_scale

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
    (hR : Phi a b - Real.logb 2 c < R)
    (hGamma : Tendsto
      (fun u : ℝ => Gamma (prependAmbient u a)
        (prependStabilizer (scaleCoordinate (c ^ 2) u) b))
      atTop (𝓝 (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b))) :
    ∃ (A : Fin (r + 2) → ℝ) (B : Fin (r + 1) → ℝ),
      Interlacing A B ∧ s < 2 * Gamma A B ∧ Phi A B < R := by
  have htarget :
      s < 2 * (((1 - c ^ 2) / 2) + c ^ 2 * Gamma a b) := by
    nlinarith
  have hspectral :
      ∀ᶠ u : ℝ in atTop,
        s < 2 * Gamma (prependAmbient u a)
          (prependStabilizer (scaleCoordinate (c ^ 2) u) b) :=
    (hGamma.const_mul 2).eventually (Ioi_mem_nhds htarget)
  have hentropy :
      ∀ᶠ u : ℝ in atTop,
        Phi (prependAmbient u a)
          (prependStabilizer (scaleCoordinate (c ^ 2) u) b) < R :=
    (tendsto_Phi_prepend_scale a b hc).eventually (Iio_mem_nhds hR)
  have hinter := eventually_interlacing_prepend_scale h hc hc'
  obtain ⟨u, hu⟩ := (hinter.and (hspectral.and hentropy)).exists
  exact ⟨prependAmbient u a,
    prependStabilizer (scaleCoordinate (c ^ 2) u) b,
    hu.1, hu.2.1, hu.2.2⟩
end MetricCodes.Spherical.HigherHierarchy
