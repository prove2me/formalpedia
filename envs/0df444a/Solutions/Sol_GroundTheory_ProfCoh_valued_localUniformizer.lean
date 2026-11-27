-- Prove2me | solution 1 for GroundTheory.ProfCoh.valued_localUniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:48:57.209212+00:00
-- url     : https://prove2.me/submissions/e83346d0-592a-4066-a7a9-de6e02230900

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
namespace GroundTheory.ProfCoh
theorem _root_.solution (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((localUniformizer v : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
  rw [localUniformizer, Units.val_mk0, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    (v.valuation_exists_uniformizer K).choose_spec]
end GroundTheory.ProfCoh
