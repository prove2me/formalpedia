-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector.allRankCartanCharacteristicProjector_youngClebschLower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/7d7cc137-2f61-4ce9-ab49-deece345d6fd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicProjector_allRankCartanCharacteristicProjector_raise_channel

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
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
theorem _root_.solution
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (h : FiniteInterlacing n target mu)
    (selected : Fin (r + 1) × Bool) (row : Fin (r + 1))
    (p : HarmonicYoungSpace (n := n) (raiseWeight target row)) :
    allRankCartanCharacteristicProjector target selected
        (youngClebschLower target (raiseWeight target row)
          (sum_raiseWeight target row) row p) =
      if selected = (row, true) then
        youngClebschLower target (raiseWeight target row)
          (sum_raiseWeight target row) row p
      else 0 := by
  exact allRankCartanCharacteristicProjector_raise_channel
    target mu h selected row
    (youngClebschLower target (raiseWeight target row)
      (sum_raiseWeight target row) row)
    (fun a b => ClebschRotation.youngClebschLower_rotation_intertwine
      target (raiseWeight target row) (sum_raiseWeight target row) row a b)
    p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
