-- Prove2me | solution 1 for GroundTheory.LocalField.mem_unitsModCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:27:08.46081+00:00
-- url     : https://prove2.me/submissions/42a34b34-d27c-4aae-9e21-04c370dacc6e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss

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
namespace GroundTheory.LocalField
theorem _root_.solution {c : ℕ} {t : unitsModFiltration K c} {x : Kˣ} :
    x ∈ unitsModCoset t ↔ (unitsModRep t)⁻¹ * x ∈ unitFiltrationUnits K c := Iff.rfl
end GroundTheory.LocalField
