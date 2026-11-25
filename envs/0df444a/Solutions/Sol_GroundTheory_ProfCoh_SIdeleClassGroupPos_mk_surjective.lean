-- Prove2me | solution 1 for GroundTheory.ProfCoh.SIdeleClassGroupPos.mk_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:33:23.380707+00:00
-- url     : https://prove2.me/submissions/67c1e1ea-56d9-47d8-914f-abf058589493

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.Global.IdeleGroup
noncomputable section
variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
open GroundTheory.ProfCoh.SIdeleClassGroupPos
namespace GroundTheory.ProfCoh.SIdeleClassGroupPos
theorem _root_.solution : Function.Surjective (mk S) := QuotientGroup.mk'_surjective _
end GroundTheory.ProfCoh.SIdeleClassGroupPos
