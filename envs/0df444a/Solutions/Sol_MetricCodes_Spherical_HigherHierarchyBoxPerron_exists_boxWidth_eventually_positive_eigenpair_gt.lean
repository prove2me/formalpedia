-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.exists_boxWidth_eventually_positive_eigenpair_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/8a253706-f27f-4f18-9077-0128bd241408

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_exists_positive_unit_topEigenpair
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyTrueGridAdjacency_matrix_symmetric
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyTrueGridAdjacency_eventually_matrix_irreducible
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_exists_boxWidth_eventually_actual_topEigenvalue_gt
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_trueGrid_matrix_eq_rectangular

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
    ∃ m : ℕ, 0 < m ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (eigenvalue : ℝ) (x : BoxVertex r m → ℝ),
          s < eigenvalue ∧
          (∀ v : BoxVertex r m, 0 < x v) ∧
          (∑ v : BoxVertex r m, x v ^ 2) = 1 ∧
          (∀ v : BoxVertex r m,
            ∑ w : BoxVertex r m,
                HigherHierarchyTrueGridAdjacency.matrix
                  (m := m) a b n v w * x w =
              eigenvalue * x v) := by
  obtain ⟨m, hm, hspectral'⟩ :=
    exists_boxWidth_eventually_actual_topEigenvalue_gt h hspectral
  refine ⟨m, hm, ?_⟩
  have hirreducible :=
    HigherHierarchyTrueGridAdjacency.eventually_matrix_irreducible
      (m := m) a b h ha hm
  filter_upwards [hspectral', hirreducible] with n hgap hconnected
  let A : Matrix (BoxVertex r m) (BoxVertex r m) ℝ :=
    HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n
  obtain ⟨x, hpositive, hunit, heigen⟩ :=
    HigherHierarchyFinitePerron.exists_positive_unit_topEigenpair
      A (HigherHierarchyTrueGridAdjacency.matrix_symmetric a b n)
      hconnected
  refine ⟨HigherHierarchyFinitePerron.topEigenvalue A,
    x, ?_, hpositive, hunit, heigen⟩
  change
    s < HigherHierarchyFinitePerron.topEigenvalue
      (HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n)
  rw [trueGrid_matrix_eq_rectangular]
  exact hgap
end MetricCodes.Spherical.HigherHierarchyBoxPerron
