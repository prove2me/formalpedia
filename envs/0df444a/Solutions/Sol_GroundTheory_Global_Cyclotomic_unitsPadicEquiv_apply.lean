-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.unitsPadicEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:12.104793+00:00
-- url     : https://prove2.me/submissions/60346f15-46df-4855-b654-ce11baa5b580

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Character
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ContinuousToZModPow
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply

set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution (u : ℤ̂ˣ) (q : Nat.Primes) :
    unitsPadicEquiv u q = Units.map (toPadicInt q).toMonoidHom u :=
  Units.ext rfl
end GroundTheory.Global.Cyclotomic
