-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.prepend_spectral_limit_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.371954+00:00
-- url     : https://prove2.me/submissions/ddf0a92f-33d7-4b38-a9b8-fb1ad2d519cb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_sum_lagrangeWeight

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
open scoped BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (c : ℝ) :
    (1 / 2 : ℝ) +
        ∑ i : Fin (r + 1),
          (c ^ 2 * lagrangeWeight a b i) *
            (spectralAtom (a i) - 1 / 2) =
      (1 - c ^ 2) / 2 + c ^ 2 * Gamma a b := by
  calc
    (1 / 2 : ℝ) +
        ∑ i : Fin (r + 1),
          (c ^ 2 * lagrangeWeight a b i) *
            (spectralAtom (a i) - 1 / 2) =
        1 / 2 +
          (c ^ 2 * (∑ i : Fin (r + 1),
            lagrangeWeight a b i * spectralAtom (a i)) -
            (c ^ 2 / 2) * (∑ i : Fin (r + 1), lagrangeWeight a b i)) := by
          congr 1
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (1 - c ^ 2) / 2 + c ^ 2 * Gamma a b := by
      rw [h.sum_lagrangeWeight]
      unfold Gamma
      ring
end MetricCodes.Spherical.HigherHierarchy
