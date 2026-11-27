-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.relIndex_powerSubgroup_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:46:25.622112+00:00
-- url     : https://prove2.me/submissions/74d12e4f-fb61-4fab-8aa8-fd8c241291e7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Theorems.Thm_GroundTheory_Global_IdeleGroup_relIndex_powerSubgroup

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
open NumberField IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup
variable (S T : Set (HeightOneSpectrum (𝓞 K)))
  (H : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (v.adicCompletion K)ˣ)
  (H' : ∀ w : InfinitePlace K, Subgroup (w.Completion)ˣ)
namespace GroundTheory.Global.IdeleGroup
theorem _root_.solution (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (powerSubgroup n S ∅).relIndex (sIdeles (S : Set (HeightOneSpectrum (𝓞 K)))) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index := by
  have h := relIndex_powerSubgroup (K := K) ∅ n S
  rwa [Set.union_empty] at h
end GroundTheory.Global.IdeleGroup
