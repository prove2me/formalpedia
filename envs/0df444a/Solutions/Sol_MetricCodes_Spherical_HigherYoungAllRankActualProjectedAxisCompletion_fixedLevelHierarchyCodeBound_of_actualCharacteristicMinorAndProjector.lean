-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion.fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/9b989023-fcaa-4110-980c-60264a4ffa2c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor_canonicalBoxAdjacentFischerRecurrence_of_minor_of_strongStable
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankActualProjectedAxisCompletion_fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence

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
    (hedges : ∀ {r m n : ℕ}
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
        ActualBoxAxisCharacteristicMinor a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i) low ∧
        ActualBoxSelectedAxisProjectorAgreement a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i)
          low row) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_extraStrongCanonicalFischerRecurrence
  intro r m n a b hinterlacing hlast hnextra hstable low high row hrow
  let hgram := fun i => canonicalBoxPositiveFischerGram a b hstable i
  obtain ⟨hminor, hselected⟩ :=
    hedges a b hinterlacing hlast hnextra hstable low high row hrow
  have hnstrong : 2 * (r + 1) + 5 ≤ n + 1 := by omega
  exact canonicalBoxAdjacentFischerRecurrence_of_minor_of_strongStable
    a b hstable hgram low high row hrow hnstrong hminor hselected
end MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
