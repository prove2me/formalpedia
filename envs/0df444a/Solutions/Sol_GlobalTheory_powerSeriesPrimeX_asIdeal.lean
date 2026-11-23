-- Prove2me | solution 1 for GlobalTheory.powerSeriesPrimeX_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:50:31.79591+00:00
-- url     : https://prove2.me/submissions/08b2b848-7b12-4fbc-a886-b6bcde6950e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_StalkGenericPointSpecializesOfSpecializes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing
universe u
open GlobalTheory
open PowerSeries
namespace GlobalTheory
theorem _root_.solution (O : Type u) [CommRing O] [IsDomain O] :
    (powerSeriesPrimeX O).asIdeal = Ideal.span {(X : O⟦X⟧)} := rfl
end GlobalTheory
