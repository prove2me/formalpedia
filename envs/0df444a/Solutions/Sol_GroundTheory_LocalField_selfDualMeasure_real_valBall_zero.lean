-- Prove2me | solution 1 for GroundTheory.LocalField.selfDualMeasure_real_valBall_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:19:58.094407+00:00
-- url     : https://prove2.me/submissions/b05d94f8-f6ae-4703-845b-7fd914c32413

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_selfDualMeasure_integers
import Theorems.Thm_GroundTheory_LocalField_coe_valBall_zero


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
    (selfDualMeasure ψ).real (valBall K 0) = (residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) := by
  rw [measureReal_def, coe_valBall_zero, selfDualMeasure_integers, ENNReal.coe_toReal,
    NNReal.coe_rpow, NNReal.coe_natCast]
end GroundTheory.LocalField
