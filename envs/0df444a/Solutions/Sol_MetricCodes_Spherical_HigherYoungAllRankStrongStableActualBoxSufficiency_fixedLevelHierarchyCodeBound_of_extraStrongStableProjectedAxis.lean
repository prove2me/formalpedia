-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency.fixedLevelHierarchyCodeBound_of_extraStrongStableProjectedAxis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/4fc056db-2a4b-40ab-b0d1-3ff85283ccc1

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankStrongStableActualBoxSufficiency_fixedLevelHierarchyCodeBound_of_extraStrongStableBoxRepresentationData

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungMovingFibres
namespace MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency
theorem _root_.solution
    (hrealization : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing n (RectangularVertices.signature a n v)
          (flooredCoordinates b n)) →
      ∃ (o : SpherePoint n)
        (fibre : (i : BoxIndex (r + 1) m) →
          BoxStabilizer n b →ₗᵢ[ℝ]
            YoungVertex (n := n) (boxSignature (m := m) a n) i),
        ∀ (target source : BoxIndex (r + 1) m)
          (h : 0 < boxProbability a b n target source),
          Nonempty (BoxProjectedAxisWitness a b o fibre target source h)) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_extraStrongStableBoxRepresentationData
  intro r m n a b hinterlacing hlast hn hstable
  obtain ⟨o, fibre, hwitness⟩ :=
    hrealization a b hinterlacing hlast hn hstable
  exact ⟨boxRepresentationData_of_projectedAxisWitnesses a b hstable
    (fun lam hd hdom =>
      weyl_dimension_eq_finrank_harmonicYoung hd lam hdom)
    o fibre (fun target source h =>
      Classical.choice (hwitness target source h))⟩
end MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency
