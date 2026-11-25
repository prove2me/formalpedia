-- Prove2me | solution 1 for GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:30.931811+00:00
-- url     : https://prove2.me/submissions/3168e6ce-894d-4d6b-8f3c-333807f53186

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
theorem _root_.solution
    (p : (InfiniteAdeleRing K)ˣ × Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletionIntegers K)ˣ) :
    (((standardOpenSubgroupEquiv K).symm p : standardOpenSubgroup K) : IdeleGroup K) =
      ofIntegerUnits p.1 p.2 :=
  rfl
end GroundTheory.Global.IdeleGroup
