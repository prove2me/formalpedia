-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.exists_boxWidth_positive_gap_eventually_positive_eigenpair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/3a89ade2-85bb-4896-b82d-189a039446ca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_exists_boxWidth_eventually_positive_eigenpair_gt

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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxPerron
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyBoxPerron
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ha : ∀ i, 0 < a i)
    {s : ℝ} (hspectral : s < 2 * HigherHierarchy.Gamma a b) :
    ∃ (m : ℕ) (gap : ℝ), 0 < m ∧ 0 < gap ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (eigenvalue : ℝ) (x : BoxVertex r m → ℝ),
          s + gap < eigenvalue ∧
          (∀ v : BoxVertex r m, 0 < x v) ∧
          (∑ v : BoxVertex r m, x v ^ 2) = 1 ∧
          (∀ v : BoxVertex r m,
            ∑ w : BoxVertex r m,
                HigherHierarchyTrueGridAdjacency.matrix
                  (m := m) a b n v w * x w =
              eigenvalue * x v) := by
  let gap : ℝ := (2 * HigherHierarchy.Gamma a b - s) / 2
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith
  have hthreshold : s + gap < 2 * HigherHierarchy.Gamma a b := by
    dsimp [gap]
    linarith
  obtain ⟨m, hm, heigen⟩ :=
    exists_boxWidth_eventually_positive_eigenpair_gt h ha hthreshold
  exact ⟨m, gap, hm, hgap, heigen⟩
end MetricCodes.Spherical.HigherHierarchyBoxPerron
