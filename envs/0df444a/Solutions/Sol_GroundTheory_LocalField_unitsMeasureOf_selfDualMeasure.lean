-- Prove2me | solution 1 for GroundTheory.LocalField.unitsMeasureOf_selfDualMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:47:49.226052+00:00
-- url     : https://prove2.me/submissions/7d45c29d-0d14-4ff0-897e-7538e9cf00a7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
import Theorems.Thm_GroundTheory_LocalField_unitsMeasureOf_eq
import Theorems.Thm_GroundTheory_LocalField_selfDualMeasure_integers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology
open scoped NNReal ENNReal
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (ψ : AddChar K Circle) :
    unitsMeasureOf (selfDualMeasure ψ) =
      ((1 - ((residueCard K : ℝ≥0∞))⁻¹) *
        (((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) : ℝ≥0∞)) • multHaar K := by
  rw [unitsMeasureOf_eq, selfDualMeasure_integers]
end GroundTheory.LocalField
