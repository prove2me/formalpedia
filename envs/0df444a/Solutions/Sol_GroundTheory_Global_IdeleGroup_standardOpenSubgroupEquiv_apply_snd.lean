-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:40.829923+00:00
-- url     : https://prove2.me/submissions/6111f9bd-cd56-4f9b-a216-bce4355905c8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (x : standardOpenSubgroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (standardOpenSubgroupEquiv K x).2 v = localIntegerUnit v x :=
  rfl
end GroundTheory.Global.IdeleGroup
