-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector.gtYoungAxisTensor_adjoint_comp_youngClebschLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/7d1aca58-50a2-4e6f-a77f-1f9d3a2c153c

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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankRawProjectedRaiseMickelsson
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowAxialAdjointGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowBaseAxisChannel
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.UniversalBGGRootComplex
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
theorem _root_.solution
    {r n : ℕ} (low high : Fin (r + 1) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 1)) (axis : SpherePacking.Euclidean n) :
    (gtYoungAxisTensor low axis).adjoint.comp
        (youngClebschLower low high hdeg row) =
      projectedCoordinateLower low high hdeg row axis := by
  apply LinearMap.ext
  intro p
  apply ext_inner_left ℝ
  intro q
  calc
    ⟪q, (gtYoungAxisTensor low axis).adjoint
        (youngClebschLower low high hdeg row p)⟫_ℝ =
      ⟪gtYoungAxisTensor low axis q,
        youngClebschLower low high hdeg row p⟫_ℝ :=
        LinearMap.adjoint_inner_right (gtYoungAxisTensor low axis)
          q (youngClebschLower low high hdeg row p)
    _ = ⟪(youngClebschLower low high hdeg row).adjoint
          (gtYoungAxisTensor low axis q), p⟫_ℝ :=
        (LinearMap.adjoint_inner_left
          (youngClebschLower low high hdeg row) p
            (gtYoungAxisTensor low axis q)).symm
    _ = ⟪projectedCoordinateRaise high low hdeg row axis q, p⟫_ℝ := by
        rw [gtYoungAxisTensor_apply,
          youngClebschLower_adjoint_tmul]
    _ = ⟪q, projectedCoordinateLower low high hdeg row axis p⟫_ℝ :=
        projectedCoordinateRaise_inner high low hdeg row axis q p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
