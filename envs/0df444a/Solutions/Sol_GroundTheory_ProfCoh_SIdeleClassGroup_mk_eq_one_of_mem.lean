-- Prove2me | solution 1 for GroundTheory.ProfCoh.SIdeleClassGroup.mk_eq_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:03:56.046751+00:00
-- url     : https://prove2.me/submissions/db51bf56-240c-4355-9234-d0792a4ecc7a

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
open GroundTheory.ProfCoh.SIdeleClassGroup
namespace GroundTheory.ProfCoh.SIdeleClassGroup
theorem _root_.solution {x : IdeleGroup K} (hx : x ∈ unitsOutside S) : mk S x = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_right hx)
end GroundTheory.ProfCoh.SIdeleClassGroup
