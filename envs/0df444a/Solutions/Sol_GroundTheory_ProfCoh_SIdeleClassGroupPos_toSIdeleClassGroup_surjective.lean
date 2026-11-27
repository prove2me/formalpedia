-- Prove2me | solution 1 for GroundTheory.ProfCoh.SIdeleClassGroupPos.toSIdeleClassGroup_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:46.473516+00:00
-- url     : https://prove2.me/submissions/9f2057a8-7415-4bbd-a182-e146ed803a7f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_SPicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_ClassFieldGSDefs
import Theorems.Thm_GroundTheory_ProfCoh_SIdeleClassGroup_mk_surjective
import Theorems.Thm_GroundTheory_ProfCoh_SIdeleClassGroupPos_mk_surjective
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_surjective


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
theorem _root_.solution : Function.Surjective (toSIdeleClassGroup S) := fun y ↦ by
  obtain ⟨x, rfl⟩ := SIdeleClassGroup.mk_surjective S y
  exact ⟨mk S x, rfl⟩
end GroundTheory.ProfCoh.SIdeleClassGroupPos
