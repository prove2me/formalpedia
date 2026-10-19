-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungActualGraphAssembly.sum_boxSignature_weyl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/da95e4a0-d40e-453d-88df-52089e627d02

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
set_option maxHeartbeats 800000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherYoungGraphAssembly
open MetricCodes.Spherical.HigherYoungMovingFibres
open MetricCodes.Spherical.HigherProjectionInstantiation
namespace MetricCodes.Spherical.HigherYoungActualGraphAssembly
theorem _root_.solution
    {r m : ℕ} (a : Fin (r + 1) → ℝ) (n : ℕ) :
    (∑ i : BoxIndex r m,
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
        (boxSignature (m := m) a n i)) =
      MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
        (m := m) a n := by
  classical
  unfold boxSignature
  unfold MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
    MetricCodes.Spherical.HigherHierarchy.RectangularVertices.vertexDimension
  exact (Fintype.equivFin
    (MetricCodes.Spherical.HigherHierarchy.RectangularVertices.Vertex
      r m)).symm.sum_comp
        (fun v : MetricCodes.Spherical.HigherHierarchy.RectangularVertices.Vertex
          r m =>
            MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
              (MetricCodes.Spherical.HigherHierarchy.RectangularVertices.signature
                a n v))
end MetricCodes.Spherical.HigherYoungActualGraphAssembly
