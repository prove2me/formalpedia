-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:09:52.53843+00:00
-- url     : https://prove2.me/submissions/fbdc9945-c472-41c5-a69b-d9519f96a54b

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
theorem _root_.solution (u : ℤ̂ˣ) (q : Nat.Primes) :
    (unitsPadicEquiv u q : ℤ_[q]) = toPadicInt q u :=
  rfl
end GroundTheory.Global.Cyclotomic
