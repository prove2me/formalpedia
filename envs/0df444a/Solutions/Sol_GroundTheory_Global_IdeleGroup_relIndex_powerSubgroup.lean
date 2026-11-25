-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.relIndex_powerSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:29:49.086998+00:00
-- url     : https://prove2.me/submissions/d7e201e9-4bee-443a-8c9e-a625f05a5c9f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex
import Theorems.Thm_GroundTheory_Global_IdeleGroup_relIndex_localSubgroup

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
    (powerSubgroup n S T).relIndex (sIdeles ((S : Set (HeightOneSpectrum (𝓞 K))) ∪ T)) =
      (∏ v ∈ S, (powMonoidHom n : (v.adicCompletion K)ˣ →* _).range.index) *
        ∏ w : InfinitePlace K, (powMonoidHom n : (w.Completion)ˣ →* _).range.index :=
  relIndex_localSubgroup T _ _ S
end GroundTheory.Global.IdeleGroup
