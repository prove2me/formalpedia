-- Prove2me | solution 1 for GroundTheory.LocalField.selfDualMeasure_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:51.634835+00:00
-- url     : https://prove2.me/submissions/9c97e61c-10b3-4e97-9eb7-1329dd08f58a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_haarIntegers_integers


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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (ψ : AddChar K Circle) :
    selfDualMeasure ψ (𝒪[K] : Set K) = ((residueCard K : ℝ≥0) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ≥0) := by
  rw [selfDualMeasure, Measure.smul_apply, haarIntegers_integers, ENNReal.smul_def, smul_eq_mul,
    mul_one]
end GroundTheory.LocalField
