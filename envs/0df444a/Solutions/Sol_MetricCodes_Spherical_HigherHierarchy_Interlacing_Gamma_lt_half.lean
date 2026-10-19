-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Interlacing.Gamma_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/9bfdb9e6-8449-4b8d-b613-f644705ac582

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_sum_lagrangeWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_spectralAtom_lt_half

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
open scoped BigOperators
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHierarchy
namespace Interlacing
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : Gamma a b < (1 / 2 : ℝ) := by
  calc
    Gamma a b =
        ∑ i : Fin (r + 1), lagrangeWeight a b i * spectralAtom (a i) := rfl
    _ < ∑ i : Fin (r + 1), lagrangeWeight a b i * (1 / 2 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
        (Finset.univ_nonempty : (Finset.univ : Finset (Fin (r + 1))).Nonempty)
      intro i _
      exact mul_lt_mul_of_pos_left (spectralAtom_lt_half (h.ambient_nonneg i))
        (h.lagrangeWeight_pos i)
    _ = (∑ i : Fin (r + 1), lagrangeWeight a b i) * (1 / 2 : ℝ) := by
      rw [Finset.sum_mul]
    _ = (1 / 2 : ℝ) := by rw [h.sum_lagrangeWeight, one_mul]
end Interlacing
end MetricCodes.Spherical.HigherHierarchy
