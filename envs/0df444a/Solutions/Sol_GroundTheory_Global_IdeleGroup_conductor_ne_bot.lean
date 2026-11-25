-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.conductor_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:21.369311+00:00
-- url     : https://prove2.me/submissions/f73d1d7f-04d0-429a-9d32-f95b5b8fb1b4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Theorems.Thm_GroundTheory_Global_finprod_asIdeal_pow_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]
omit [TopologicalSpace H]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : conductor χ ≠ ⊥ :=
  finprod_asIdeal_pow_ne_bot _
end GroundTheory.Global.IdeleGroup
