-- Prove2me | solution 1 for GroundTheory.Global.prime_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:52:45.83992+00:00
-- url     : https://prove2.me/submissions/14d063d9-43a2-4bcf-9499-a1389e37e510

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant

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
namespace GroundTheory.Global
theorem _root_.solution {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F)) :
    Prime u.asIdeal :=
  Ideal.prime_of_isPrime u.ne_bot u.isPrime
end GroundTheory.Global
