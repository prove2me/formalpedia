-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.fixedLevelCompactifiedCertificateClosure_of_forward_residual_and_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/bd40dcdd-f8dc-4aa1-b65f-01badc69728a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_certificate_entropy_le
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_certificate_residual_threshold_le

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
    {r : ℕ}
    (hforward : FixedLevelForwardCompactifiedResidualLimit r)
    (hrealize : ∀ {j : ℕ} {s c : ℝ}
      (A : Fin (j + 1) → ℝ) (B : Fin j → ℝ),
      0 < s → s < 1 → 0 < c → c ≤ 1 →
      Interlacing A B →
      s ≤ 1 - c ^ 2 * (1 - 2 * Gamma A B) →
      ((c = 1 ∧ j ≤ r) ∨ (c < 1 ∧ j + 1 ≤ r)) →
      levelRate r s ≤ Phi A B - Real.logb 2 c) :
    FixedLevelCompactifiedCertificateClosure r := by
  intro s R hs hs' u a b hu hinter hgap hPhi
  have huniform : ∀ n, Phi (a n) (b n) ≤ R + 1 := by
    intro n
    calc
      Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1) := hPhi n
      _ ≤ R + 1 := by
        apply add_le_add (le_refl R)
        apply (div_le_iff₀ (by positivity)).2
        norm_num
  obtain ⟨j, c, A, B, φ, hφ, hc, hc', hAB,
    hlevels, hGamma, hentropy⟩ := hforward a b hinter huniform
  have hclosed := compactified_certificate_residual_threshold_le
    hφ hu hgap hGamma
  have hbound := compactified_certificate_entropy_le
    hφ hPhi hentropy
  exact (hrealize A B hs hs' hc hc' hAB hclosed hlevels).trans hbound
end MetricCodes.Spherical.HigherHierarchy
