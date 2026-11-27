-- Prove2me | solution 1 for GroundTheory.Global.absNorm_relDiscr_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:29.080959+00:00
-- url     : https://prove2.me/submissions/e842df99-5db1-433c-82c3-dc0d39a70f67

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
import Theorems.Thm_GroundTheory_Global_differentIdeal_ringOfIntegers_rat

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
variable (M : Type*) [Field M] [NumberField M]
namespace GroundTheory.Global
theorem _root_.solution : Ideal.absNorm (relDiscr ℚ M) = (discr M).natAbs := by
  rw [relDiscr, Ideal.absNorm_relNorm, differentIdeal_ringOfIntegers_rat,
    absNorm_differentIdeal M]
end GroundTheory.Global
