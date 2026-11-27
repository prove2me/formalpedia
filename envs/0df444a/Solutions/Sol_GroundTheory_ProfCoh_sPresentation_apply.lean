-- Prove2me | solution 1 for GroundTheory.ProfCoh.sPresentation_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:49:52.704044+00:00
-- url     : https://prove2.me/submissions/25072167-04b6-4f38-8376-6a19cf2fa7eb

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
theorem _root_.solution [Finite S] (a : ∀ w : S, (w.1.adicCompletion K)ˣ)
    (D : Multiplicative (sDivisor S)) :
    sPresentation S (a, D) =
      SIdeleClassGroup.mk S (placesIdele S a * Additive.toMul (divisorIdele S D.toAdd)) :=
  rfl
end GroundTheory.ProfCoh
