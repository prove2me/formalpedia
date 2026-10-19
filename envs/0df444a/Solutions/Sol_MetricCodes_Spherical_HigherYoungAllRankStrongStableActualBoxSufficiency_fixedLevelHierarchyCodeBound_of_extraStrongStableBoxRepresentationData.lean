-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency.fixedLevelHierarchyCodeBound_of_extraStrongStableBoxRepresentationData
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/9bd12aae-ebc8-443c-be8b-9c0b1d072ac3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_finiteInterlacing_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_exists_boxWidth_positive_gap_eventually_positive_eigenpair
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
import Theorems.Thm_MetricCodes_Spherical_HigherYoungActualGraphAssembly_actualYoungBox_rankQuotient_eq_weyl

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
    (hrepresentation : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
        Interlacing a b → 0 < a (Fin.last (r + 1)) →
        2 * (r + 2) + 5 ≤ n →
        (∀ v : RectangularVertices.Vertex (r + 1) m,
          FiniteInterlacing n (RectangularVertices.signature a n v)
            (flooredCoordinates b n)) →
        Nonempty (BoxRepresentationData (m := m) (n := n) a b)) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_actualRectangularGraphs
  intro r s R hs hs' a b hinterlacing hlast hspectral hR
  have hpositive : ∀ i : Fin (r + 2), 0 < a i := by
    intro i
    exact hlast.trans_le
      (hinterlacing.strictAnti_ambient.antitone i.le_last)
  obtain ⟨m, gap, _hm, hgap, hperron⟩ :=
    HigherHierarchyBoxPerron.exists_boxWidth_positive_gap_eventually_positive_eigenpair
      hinterlacing hpositive hspectral
  let stable : ℕ → Prop := fun n =>
    2 * (r + 2) + 5 ≤ n ∧
      (∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing n (RectangularVertices.signature a n v)
          (flooredCoordinates b n)) ∧
      Nonempty (BoxPerronData (m := m) (n := n) a b s gap)
  letI : DecidablePred stable := Classical.decPred stable
  have heventual : ∀ᶠ n : ℕ in atTop, stable n := by
    filter_upwards
      [eventually_ge_atTop (2 * (r + 2) + 5),
        RectangularVertices.eventually_finiteInterlacing_all
          (m := m) a b hinterlacing, hperron] with n hn hinter he
    refine ⟨hn, hinter, ?_⟩
    obtain ⟨eigenvalue, eigenvector, hmargin, hpos, hunit, heq⟩ := he
    exact ⟨⟨eigenvalue, eigenvector, hmargin, hpos, hunit, heq⟩⟩
  let D : (n : ℕ) → stable n →
      BoxRepresentationData (m := m) (n := n) a b :=
    fun n h => Classical.choice
      (hrepresentation a b hinterlacing hlast h.1 h.2.1)
  let P : (n : ℕ) → (h : stable n) →
      BoxPerronData (m := m) (n := n) a b s gap :=
    fun n h => Classical.choice h.2.2
  let H : (n : ℕ) → (h : stable n) →
      RealizedHilbertGraph
        (BoxIndex (r + 1) m) (SpherePoint n) (BoxStabilizer n b)
        (YoungAmbient n (boxSignature (m := m) a n))
        (YoungCoordinateAmbient n (boxSignature (m := m) a n)) :=
    fun n h =>
      (D n h).toHilbertGraph h.2.1 (P n h).eigenvalue
        (by linarith [(P n h).spectral_gap])
        (P n h).eigenvector (P n h).positive (P n h).unit
        (P n h).equation
  let G : (n : ℕ) → stable n → IndexedHierarchyGraph n :=
    fun n h => actualYoungIndexedHierarchyGraph
      (boxSignature (m := m) a n) (H n h)
  refine ⟨m, gap, hgap, stable, inferInstance, heventual, G,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro n h
    change 0 < Fintype.card (RectangularVertices.Vertex (r + 1) m)
    exact Fintype.card_pos_iff.mpr ⟨fun _ => 0⟩
  · intro n h
    exact (D n h).stabilizer_pos
  · intro n h x y
    rfl
  · exact Filter.Eventually.of_forall fun n h => (P n h).spectral_gap
  · apply Filter.Eventually.of_forall
    intro n h
    exact actualYoungBox_rankQuotient_eq_weyl a b (H n h)
      (fun _ => rfl) (D n h).vertex_weyl (D n h).stabilizer_weyl
end MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency
