-- Prove2me | solution 1 for GroundTheory.LocalField.measurableSet_unitsModCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:14.386584+00:00
-- url     : https://prove2.me/submissions/8c053408-420c-4bde-96c8-7f96f30ef100

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Theorems.Thm_GroundTheory_LocalField_isOpen_unitFiltrationUnits


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
theorem _root_.solution {c : ℕ} (t : unitsModFiltration K c) :
    MeasurableSet (unitsModCoset t) :=
  (isOpen_unitFiltrationUnits c).measurableSet.preimage (measurable_const_mul _)
end GroundTheory.LocalField
