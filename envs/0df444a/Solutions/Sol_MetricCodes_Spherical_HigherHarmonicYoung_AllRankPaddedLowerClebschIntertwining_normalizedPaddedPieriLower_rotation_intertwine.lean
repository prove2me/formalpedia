-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining.normalizedPaddedPieriLower_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/bf56cc44-d1cb-4a2b-a545-95b1165d910c

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
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankInternalRowLowerGram
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowDownstreamActualChannels
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungArbitraryRowLoweringProjectedAxisWitness
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
theorem _root_.solution
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (hdominant : Antitone target)
    (row : Fin (r + 1))
    (hsource : Antitone (raiseWeight target row))
    (i j : Fin n) :
    (normalizedPaddedPieriLower (n := n)
      target hdominant row hsource).toLinearMap.comp
        (youngAmbientRotation (raiseWeight target row) i j) =
      (ClebschRotation.tensorAmbientRotation target i j).comp
        (normalizedPaddedPieriLower (n := n)
          target hdominant row hsource).toLinearMap := by
  exact boundaryNormalizedYoungClebschLower_rotation_intertwine
    target (raiseWeight target row) (sum_raiseWeight target row) row
    (internalRowLowerGramScalar (raiseWeight target row) row)
    (internalRowLowerGramScalar_pos (raiseWeight target row) row
      (by simp [raiseWeight])
      (raiseWeight_strictly_removable target hdominant row))
    (youngClebschLower_inner_of_raisedSignature
      (raiseWeight target row) target row
      (loweredInternalYoungWeight_raiseWeight target row).symm
      (by simp [raiseWeight]) hsource
      (sum_raiseWeight target row))
    i j
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankPaddedLowerClebschIntertwining
