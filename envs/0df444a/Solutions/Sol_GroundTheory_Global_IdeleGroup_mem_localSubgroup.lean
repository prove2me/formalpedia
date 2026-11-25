-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.mem_localSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:24:05.275803+00:00
-- url     : https://prove2.me/submissions/7e3dac97-3ea4-4862-ac3f-2c246443b2f4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_SIdeleGroups
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndexAtPlace
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalConditionIndex

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
theorem _root_.solution {x : IdeleGroup K} :
    x ∈ localSubgroup S T H H' ↔ (∀ v ∈ S, finiteProj v x ∈ H v) ∧
      (∀ w, infiniteProj w x ∈ H' w) ∧ ∀ v ∉ S ∪ T, ord v x = 0 :=
  Iff.rfl
end GroundTheory.Global.IdeleGroup
