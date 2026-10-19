-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport.upperPolarizationPathCommutator_append_pivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/9d60de4d-9fff-441e-b2be-37d518ee5241

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
theorem _root_.solution
    {r n : ℕ} (pivot target : Fin (r + 1)) (hpt : pivot < target)
    (front : List (Fin (r + 1))) (hnon : front ≠ [])
    (hfront : ∀ a ∈ front, a < pivot) :
    upperPolarizationPathCommutator (n := n) target pivot
        (front ++ [pivot]) =
      lowerPolarizationPath (n := n) (front ++ [target]) := by
  induction front with
  | nil => exact False.elim (hnon rfl)
  | cons first rest ih =>
      have hfirst : first < pivot := hfront first (by simp)
      have hfirstTarget : first ≠ target :=
        ne_of_lt (hfirst.trans hpt)
      cases rest with
      | nil =>
          simp [upperPolarizationPathCommutator,
            lowerPolarizationPath, hfirstTarget]
      | cons second tail =>
          have hsecond : second < pivot := hfront second (by simp)
          have hpivotSecond : pivot ≠ second := ne_of_gt hsecond
          have hrest : ∀ a ∈ (second :: tail), a < pivot := by
            intro a ha
            exact hfront a (by simp [ha])
          change
            (polarization r n second first).comp
                  (upperPolarizationPathCommutator target pivot
                    ((second :: tail) ++ [pivot])) +
                (if pivot = second then
                  (polarization r n target first).comp
                    (lowerPolarizationPath ((second :: tail) ++ [pivot]))
                else 0) -
                (if first = target then
                  (polarization r n second pivot).comp
                    (lowerPolarizationPath ((second :: tail) ++ [pivot]))
                else 0) =
              (polarization r n second first).comp
                (lowerPolarizationPath ((second :: tail) ++ [target]))
          rw [if_neg hpivotSecond, if_neg hfirstTarget,
            ih (by simp) hrest]
          simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralRootTransport
