-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector.allRankCartanCharacteristicProjector_raise_channel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/a4c54d09-c6bf-404c-a251-26b2a64132ed

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_raise_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicProjector_allRankCartanCharacteristicProjector_apply_eigenvector

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
    (A : HarmonicYoungSpace (n := n) (raiseWeight target row) →ₗ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ a b : Fin n,
      A.comp (youngAmbientRotation (raiseWeight target row) a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp A)
    (p : HarmonicYoungSpace (n := n) (raiseWeight target row)) :
    allRankCartanCharacteristicProjector target selected (A p) =
      if selected = (row, true) then A p else 0 := by
  apply allRankCartanCharacteristicProjector_apply_eigenvector
    target mu h selected (row, true) (A p)
  exact gtRelativeCasimir_raise_channel target row A hA p
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
