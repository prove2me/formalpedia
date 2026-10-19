-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan.canonicalGelfandTsetlinAxisTensor_mem_gtSelectedPhysicalSignedSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/0a474f86-9ff6-4231-a9af-4de1da2ae203

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedPhysicalChannelRange_selectedSignedEigenspace_le_youngClebschLower_range
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTSelectedRestrictedProjectorEquality_gtSignedEigenvectorSpan_le_selectedPhysicalSignedSpan
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseOrthogonalCompleteness_canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan

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
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedPhysicalChannelRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseOrthogonalCompleteness
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 2) → ℕ)
    (mu : Fin (r + 1) → ℕ) (h : Interlaces low mu)
    (hgram : PositiveGelfandTsetlinFischerGram (n := n) low mu h)
    (hfinite : FiniteInterlacing (n + 1) low mu)
    (hdom : Antitone low) (row : Fin (r + 2))
    (hhigh : Antitone (raiseWeight low row))
    (hn : 2 * (r + 2) + 5 ≤ n + 1)
    (p : HarmonicYoungSpace (n := n) mu) :
    canonicalGelfandTsetlinAxisTensor low mu h hgram p ∈
      gtSelectedPhysicalSignedSpan (n := n + 1) low row := by
  apply gtSignedEigenvectorSpan_le_selectedPhysicalSignedSpan
    low row
      (selectedSignedEigenspace_le_youngClebschLower_range
        (by omega) low mu hfinite hdom row hhigh)
  exact canonicalGelfandTsetlinAxisTensor_mem_gtSignedEigenvectorSpan
    low mu h hn hgram p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCanonicalPhysicalSignedSpan
