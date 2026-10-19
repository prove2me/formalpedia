-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion.fixedLevelHierarchyCodeBound_of_actualCharacteristicMinor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/c58b6b75-4101-473c-94cc-fbf0a5ebc02a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCanonicalPhysicalSignedSpan_allRankCartanCharacteristicProjector_canonicalAxis_eq_physicalClebsch
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankActualProjectedAxisCompletion_fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector

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
    (hminor : ∀ {r m n : ℕ}
      (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ),
      Interlacing a b → 0 < a (Fin.last (r + 1)) →
      2 * (r + 2) + 5 ≤ n + 1 →
      (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
        FiniteInterlacing (n + 1)
          (RectangularVertices.signature a (n + 1) v)
          (flooredCoordinates b (n + 1))) →
      ∀ low : BoxIndex (r + 1) m,
        ActualBoxAxisCharacteristicMinor a b hstable
          (fun i => canonicalBoxPositiveFischerGram a b hstable i) low) :
    FixedLevelHierarchyCodeBound := by
  apply fixedLevelHierarchyCodeBound_of_actualCharacteristicMinorAndProjector
  intro r m n a b hinterlacing hlast hn hstable low high row hrow
  refine ⟨hminor a b hinterlacing hlast hn hstable low, ?_⟩
  let lam := boxSignature (m := m) a (n + 1) low
  let mu := Weyl.flooredWeight b (n + 1)
  let h := boxSignature_interlaces a b hstable low
  let hgram := canonicalBoxPositiveFischerGram a b hstable low
  have hfinite : FiniteInterlacing (n + 1) lam mu := by
    constructor
    · exact (hstable
        ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low)).1
    · exact h
  have hdom : Antitone lam := h.antitone_ambient
  have hhigh : Antitone (raiseWeight lam row) := by
    rw [← hrow]
    exact (boxSignature_interlaces a b hstable high).antitone_ambient
  intro p
  exact allRankCartanCharacteristicProjector_canonicalAxis_eq_physicalClebsch
    lam mu h hgram hfinite hdom row hhigh hn p
end MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisCompletion
