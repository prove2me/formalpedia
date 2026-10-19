-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion.fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/dbddc076-c02f-4787-ab2c-41ea371e4cee

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalBoxActualForward_canonicalBoxForwardPolynomialData_of_recurrence
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankCanonicalBoxReverseRange_canonicalBoxReverseAxisRange_of_strongStable
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankStrongStableActualBoxSufficiency_fixedLevelHierarchyCodeBound_of_extraStrongStableProjectedAxis

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
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxProjectedAxisWitness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherProjectionInstantiation
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
open MetricCodes.Spherical.HigherYoungAllRankCanonicalBoxReverseRange
open MetricCodes.Spherical.HigherYoungAllRankStrongStableActualBoxSufficiency
namespace MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
theorem _root_.solution
    (hrecurrence : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ (low high : BoxIndex (r + 1) m)
        (row : Fin (r + 2))
        (_ : boxSignature (m := m) a (n + 1) high =
          raiseWeight (boxSignature (m := m) a (n + 1) low) row),
        CanonicalBoxAdjacentFischerRecurrence a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low high row) :
    FixedLevelHierarchyCodeBound := by
  classical
  apply fixedLevelHierarchyCodeBound_of_extraStrongStableProjectedAxis
  intro r m n a b hinterlacing hlast hnextra hstable
  cases n with
  | zero => omega
  | succ n =>
      have hnstrong : 2 * (r + 1) + 5 ≤ n + 1 := by omega
      let hgram := fun i => canonicalBoxPositiveFischerGram a b hstable i
      let fibre := canonicalBoxGelfandTsetlinFibre a b hstable hgram
      let o := boxAxis (n + 1) (by omega)
      refine ⟨o, fibre, ?_⟩
      intro target source h
      refine ⟨canonicalBoxProjectedAxisWitness a b hstable hgram o ?_
        target source h⟩
      intro low high row hrow
      exact canonicalBoxEdgeAxisData_of_polynomialData a b hstable hgram
        low high row hrow
        (canonicalBoxForwardPolynomialData_of_recurrence
          a b hstable hgram low high row hrow
          (hrecurrence a b hinterlacing hlast hnextra hstable
            low high row hrow))
        (canonicalBoxReverseAxisRange_of_strongStable a b hstable hgram
          hnstrong low high row hrow)
end MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
