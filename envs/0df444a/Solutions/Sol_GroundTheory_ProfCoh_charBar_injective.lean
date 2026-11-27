-- Prove2me | solution 1 for GroundTheory.ProfCoh.charBar_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:50:55.385435+00:00
-- url     : https://prove2.me/submissions/b149f34d-428f-4e7b-ba0f-0d67f475a9b5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCup
import Definitions.Def_GroundTheory_TateCohomology_InfRes
import Definitions.Def_GroundTheory_ProfiniteCohomology_CyclicCupInflation

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
open CategoryTheory Limits MonoidalCategory groupCohomology GroundTheory.GroupCoh
variable {G : Type} [Group G]
namespace GroundTheory.ProfCoh
theorem _root_.solution (χ : Additive G →+ AddCircle (1 : ℚ)) :
    Function.Injective (charBar χ) := by
  intro x y h
  apply Additive.toMul.injective
  apply QuotientGroup.kerLift_injective (AddMonoidHom.toMultiplicativeRight χ)
  exact congrArg Multiplicative.ofAdd h
end GroundTheory.ProfCoh
