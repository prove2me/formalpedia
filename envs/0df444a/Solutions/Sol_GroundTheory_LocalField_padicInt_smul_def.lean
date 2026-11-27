-- Prove2me | solution 1 for GroundTheory.LocalField.padicInt_smul_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:46:54.355881+00:00
-- url     : https://prove2.me/submissions/e79efeda-2ca3-494a-bb7d-03441aba4ead

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicExp
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule

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
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]
namespace GroundTheory.LocalField
theorem _root_.solution (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    a • u = padicIntSMul p a u := rfl
end GroundTheory.LocalField
