-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.continuous_toZModPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:12.875298+00:00
-- url     : https://prove2.me/submissions/2addebae-caa7-4c67-8bf4-e6f4109a86c8

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_UpperTheory_Reformulated_B_Yde3_continuous_toZModPow


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
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (n : ℕ) : Continuous (PadicInt.toZModPow (p := ℓ) n) :=
  _root_.UpperTheory.Reformulated.B.Yde3.continuous_toZModPow n
end GroundTheory.Global.Cyclotomic
