-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungActualGraphAssembly.actualYoungBox_rankQuotient_eq_weyl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/1c0e3657-b416-4a81-9f46-80e1974e5ac0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungActualGraphAssembly_sum_boxSignature_weyl

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
    {r m n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (G : RealizedHilbertGraph (BoxIndex (r + 1) m) (SpherePoint n) E
      (YoungAmbient n (boxSignature (m := m) a n))
      (YoungCoordinateAmbient n (boxSignature (m := m) a n)))
    (hdimension : ∀ i : BoxIndex (r + 1) m,
      G.dimension i = Module.finrank ℝ
        (YoungVertex (n := n) (boxSignature (m := m) a n) i))
    (hweyl : ∀ i : BoxIndex (r + 1) m,
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
        (boxSignature (m := m) a n i) =
        (Module.finrank ℝ
          (YoungVertex (n := n) (boxSignature (m := m) a n) i) : ℝ))
    (hfibre :
      MetricCodes.Spherical.HigherHierarchy.Weyl.dimension (n - 1)
        (MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight b
          n) = (Module.finrank ℝ E : ℝ)) :
    ((∑ i : Fin
        (actualYoungIndexedHierarchyGraph
          (boxSignature (m := m) a n) G).vertexCount,
      ((actualYoungIndexedHierarchyGraph
        (boxSignature (m := m) a n) G).graph.dimension i : ℝ)) /
      ((actualYoungIndexedHierarchyGraph
        (boxSignature (m := m) a n) G).fibreDimension : ℝ)) =
      MetricCodes.Spherical.HigherHierarchy.RectangularVertices.dimensionSum
        (m := m) a n /
        MetricCodes.Spherical.HigherHierarchy.Weyl.dimension (n - 1)
          (MetricCodes.Spherical.HigherHierarchy.Weyl.flooredWeight b
            n) := by
  change
    (∑ i : BoxIndex (r + 1) m, (G.dimension i : ℝ)) /
        (Module.finrank ℝ E : ℝ) = _
  rw [← hfibre]
  congr 1
  calc
    (∑ i : BoxIndex (r + 1) m, (G.dimension i : ℝ)) =
        ∑ i : BoxIndex (r + 1) m,
          MetricCodes.Spherical.HigherHierarchy.Weyl.dimension n
            (boxSignature (m := m) a n i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hdimension i, ← hweyl i]
    _ = _ := sum_boxSignature_weyl a n
end MetricCodes.Spherical.HigherYoungActualGraphAssembly
