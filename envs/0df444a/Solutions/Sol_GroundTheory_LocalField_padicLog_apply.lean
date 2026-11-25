-- Prove2me | solution 1 for GroundTheory.LocalField.padicLog_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:29:31.152991+00:00
-- url     : https://prove2.me/submissions/f9884cf1-7df4-4f5d-8754-182cc93095bb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (K) [CharZero K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution (u : Additive (unitFiltrationUnits K 1)) :
    padicLog K u = logSeries ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) :=
  rfl
end GroundTheory.LocalField
