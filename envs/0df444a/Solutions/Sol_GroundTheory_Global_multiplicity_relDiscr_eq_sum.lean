-- Prove2me | solution 1 for GroundTheory.Global.multiplicity_relDiscr_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:50:06.841532+00:00
-- url     : https://prove2.me/submissions/97b728e7-c088-4626-965d-6aa9a3c9e7ba

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Theorems.Thm_GroundTheory_Global_multiplicity_relNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
variable (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution :
    multiplicity v.asIdeal (relDiscr K M) =
      ∑ w : SemiLocal.PlacesOver M v,
        w.1.asIdeal.inertiaDeg (𝓞 K) * multiplicity w.1.asIdeal (differentIdeal (𝓞 K) (𝓞 M)) :=
  multiplicity_relNorm v _ differentIdeal_ne_bot
end GroundTheory.Global
