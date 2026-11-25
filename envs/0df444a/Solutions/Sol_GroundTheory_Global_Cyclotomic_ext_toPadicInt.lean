-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.ext_toPadicInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:12:01.54923+00:00
-- url     : https://prove2.me/submissions/1dac7b3e-67d0-4b83-ab06-745329d998a0

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadics_injective

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
theorem _root_.solution {x y : ℤ̂} (h : ∀ q : Nat.Primes, toPadicInt q x = toPadicInt q y) :
    x = y :=
  toPadics_injective (funext h)
end GroundTheory.Global.Cyclotomic
