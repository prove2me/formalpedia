-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor.canonicalBoxAdjacentFischerRecurrence_of_minor_of_strongStable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/f2035bfb-20d7-4b3a-9d06-1eed3c0adb47

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankInterlacingAdjacentPathExchange_reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCanonicalBoxActualForward_dominantSameAxisDiamond_allRows
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankActualFischerGramRecurrence_canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedPhysicalAxisRange_reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor_of_strongStable

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxActualForward
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalAxisRange
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyActualBoxSufficiency
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungActualGraphAssembly
open MetricCodes.Spherical.HigherYoungAllRankActualBoxInstantiation
open MetricCodes.Spherical.HigherYoungAllRankActualProjectedAxisAssembly
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor
theorem _root_.solution
    {r m n : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hstable : ∀ v : RectangularVertices.Vertex (r + 1) m,
      FiniteInterlacing (n + 1)
        (RectangularVertices.signature a (n + 1) v)
        (flooredCoordinates b (n + 1)))
    (hgram : ∀ i : BoxIndex (r + 1) m,
      PositiveGelfandTsetlinFischerGram (n := n)
        (boxSignature (m := m) a (n + 1) i)
        (Weyl.flooredWeight b (n + 1))
        (boxSignature_interlaces a b hstable i))
    (low high : BoxIndex (r + 1) m) (row : Fin (r + 2))
    (hrow : boxSignature (m := m) a (n + 1) high =
      raiseWeight (boxSignature (m := m) a (n + 1) low) row)
    (hnstrong : 2 * (r + 1) + 5 ≤ n + 1)
    (hminor : ∀ p q : HarmonicYoungSpace (n := n)
        (Weyl.flooredWeight b (n + 1)),
      gtAxisCompressedCharacteristicMinor
          (boxSignature (m := m) a (n + 1) low)
          (Weyl.flooredWeight b (n + 1))
          (boxSignature_interlaces a b hstable low)
          (hgram low) p q =
        Polynomial.C ⟪p, q⟫_ℝ *
          channelNumeratorPolynomial (wallShift (n + 1) (r + 1))
            (HigherChannel.stabilizerShift (n + 1)
              (Weyl.flooredWeight b (n + 1))))
    (hselected : ∀ p : HarmonicYoungSpace (n := n)
        (Weyl.flooredWeight b (n + 1)),
      allRankCartanCharacteristicProjector
          (boxSignature (m := m) a (n + 1) low) (row, true)
          (canonicalGelfandTsetlinAxisTensor
            (boxSignature (m := m) a (n + 1) low)
            (Weyl.flooredWeight b (n + 1))
            (boxSignature_interlaces a b hstable low) (hgram low) p) =
        gtSelectedRowClebschRangeProjector
          (boxSignature (m := m) a (n + 1) low) row
          (canonicalGelfandTsetlinAxisTensor
            (boxSignature (m := m) a (n + 1) low)
            (Weyl.flooredWeight b (n + 1))
            (boxSignature_interlaces a b hstable low) (hgram low) p)) :
    CanonicalBoxAdjacentFischerRecurrence
      a b hstable hgram low high row := by
  let lam := boxSignature (m := m) a (n + 1) low
  let mu := Weyl.flooredWeight b (n + 1)
  have hfinite : FiniteInterlacing (n + 1) lam mu := by
    exact hstable
      ((Fintype.equivFin (RectangularVertices.Vertex (r + 1) m)).symm low)
  have hn : 2 * (r + 1) ≤ n := by
    have hbound := box_stableRange a b hstable
    omega
  let hlow : Interlaces lam mu := boxSignature_interlaces a b hstable low
  have hhigh : Interlaces (raiseWeight lam row) mu := by
    rw [← hrow]
    exact boxSignature_interlaces a b hstable high
  have hhighGram : PositiveGelfandTsetlinFischerGram
      (n := n) (raiseWeight lam row) mu hhigh := by
    simpa only [lam, mu, hrow] using (hgram high)
  obtain ⟨p, hp⟩ :=
    DeterminantVectors.exists_nonzero_harmonicYoung_of_antitone
      hn mu (interlaces_antitone_stabilizer hlow)
  have hresult :=
    AllRankActualFischerGramRecurrence.canonicalGelfandTsetlinFischerGram_adjacent_of_projectedLower
      lam mu row hlow hhigh hlow.antitone_ambient
      (hgram low) hhighGram
      (fun q => by
        rw [ArbitraryRankInterlacingAdjacentPathExchange.reverseInterlacingPolynomialSeed_adjacent_raise_of_diamond
          (dominantSameAxisDiamond_allRows (r + 1) (n + 1)) hlow row q,
          sub_self]
        exact (youngGramRadialIdeal (r + 1) (n + 1)).zero_mem)
      (reverseInterlacing_projectedCoordinateLower_sameAxis_eq_plusProbability_of_minor_of_strongStable
        lam mu row hnstrong hlow hhigh (hgram low) hfinite
        hlow.antitone_ambient hminor hselected)
      p hp
  simpa only [CanonicalBoxAdjacentFischerRecurrence, lam, mu, hrow]
    using hresult
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalBoxFischerRecurrenceOfCharacteristicMinor
