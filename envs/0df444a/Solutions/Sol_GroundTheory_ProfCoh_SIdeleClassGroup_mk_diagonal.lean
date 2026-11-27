-- Prove2me | solution 1 for GroundTheory.ProfCoh.SIdeleClassGroup.mk_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:48:34.813522+00:00
-- url     : https://prove2.me/submissions/eac00a39-e144-4dc4-836b-15d9921556b5

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
theorem _root_.solution (a : Kˣ) : mk S (diagonal K a) = 1 :=
  (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_sup_left ⟨a, rfl⟩)
end GroundTheory.ProfCoh.SIdeleClassGroup
