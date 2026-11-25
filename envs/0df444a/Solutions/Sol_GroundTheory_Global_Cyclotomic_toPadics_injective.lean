-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.toPadics_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:16.272886+00:00
-- url     : https://prove2.me/submissions/93698cf2-a9df-4252-98bf-176cbe0ec5ff

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution : Function.Injective toPadics :=
  padicEquiv.injective
end GroundTheory.Global.Cyclotomic
