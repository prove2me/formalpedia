-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality.gtSignedEigenvectorSpan_le_selectedPhysicalSignedSpan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/69fd085d-91f3-436c-acb0-a8a2e140a41f

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
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hselected :
      Module.End.eigenspace (gtRelativeCasimir (n := n) low)
        (signedNode (HigherChannel.ambientShift n low) (row, true)) ≤
      LinearMap.range
        (youngClebschLower low (raiseWeight low row)
          (sum_raiseWeight low row) row)) :
    gtSignedEigenvectorSpan (n := n) low ≤
      gtSelectedPhysicalSignedSpan (n := n) low row := by
  unfold gtSignedEigenvectorSpan gtSelectedPhysicalSignedSpan
  apply iSup_le
  intro channel
  by_cases hchannel : channel = (row, true)
  · subst channel
    exact hselected.trans le_sup_left
  · exact
      (le_iSup
        (fun channel : {channel : Fin (r + 1) × Bool //
          channel ≠ (row, true)} =>
          Module.End.eigenspace (gtRelativeCasimir (n := n) low)
            (signedNode (HigherChannel.ambientShift n low) channel.val))
        ⟨channel, hchannel⟩).trans le_sup_right
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
