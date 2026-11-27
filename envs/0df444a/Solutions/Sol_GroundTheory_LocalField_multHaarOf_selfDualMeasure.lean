-- Prove2me | solution 1 for GroundTheory.LocalField.multHaarOf_selfDualMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:54:55.296712+00:00
-- url     : https://prove2.me/submissions/b19ecc1a-b432-4832-8225-af8f216f8bda

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
import Definitions.Def_GroundTheory_LocalFields_LocalFourierMult
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
    multHaarOf (selfDualMeasure ψ) =
      (((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) : ℝ≥0∞) • multHaar K := by
  rw [multHaarOf_eq, selfDualMeasure_integers]
end GroundTheory.LocalField
