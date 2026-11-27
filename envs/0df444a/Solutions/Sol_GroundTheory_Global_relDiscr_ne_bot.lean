-- Prove2me | solution 1 for GroundTheory.Global.relDiscr_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:03.280024+00:00
-- url     : https://prove2.me/submissions/efb9581c-8cf1-4722-98dc-3a3eea8077f6

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
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
namespace GroundTheory.Global
theorem _root_.solution : relDiscr K M ≠ ⊥ := by
  rw [relDiscr, Ne, Ideal.relNorm_eq_bot_iff]
  exact differentIdeal_ne_bot
end GroundTheory.Global
