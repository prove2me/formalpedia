-- Prove2me | solution 1 for GlobalTheory.star_form_eq_of_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:50.0126+00:00
-- url     : https://prove2.me/submissions/01846200-b192-457c-ab07-8c2b6b3c95c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryMulVecEqOfFormEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {E : Type} [Field E] [StarRing E] {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (z w : Fin n → E) :
    star (star z ⬝ᵥ (J *ᵥ w)) = star w ⬝ᵥ (J *ᵥ z) := by
  rw [star_dotProduct z (J *ᵥ w), star_star, star_mulVec, ← dotProduct_mulVec, hJ]
end GlobalTheory
