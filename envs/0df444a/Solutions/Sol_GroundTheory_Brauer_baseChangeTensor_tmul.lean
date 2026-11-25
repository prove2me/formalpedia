-- Prove2me | solution 1 for GroundTheory.Brauer.baseChangeTensor_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:34.849851+00:00
-- url     : https://prove2.me/submissions/1b589284-187e-4815-a945-ab58df9cf4aa

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Algebra.TensorProduct
variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Semiring A]
  [Algebra K A] [Semiring B] [Algebra K B]
namespace GroundTheory.Brauer
theorem _root_.solution (l : L) (a : A) (b : B) :
    baseChangeTensor K L A B (l ⊗ₜ (a ⊗ₜ b)) = (l ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b) := rfl
end GroundTheory.Brauer
