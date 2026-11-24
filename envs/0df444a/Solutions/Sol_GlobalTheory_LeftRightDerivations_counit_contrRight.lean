-- Prove2me | solution 1 for GlobalTheory.LeftRightDerivations.counit_contrRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:40:06.688286+00:00
-- url     : https://prove2.me/submissions/f7fe51db-f60c-4308-96b9-f7082fae5e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsCounitDerivationCounitComp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.LeftRightDerivations
variable {k : Type*} {H : Type*} [CommSemiring k] [CommSemiring H] [Bialgebra k H]
namespace GlobalTheory.LeftRightDerivations
theorem _root_.solution (φ : H →ₗ[k] k) (s : H ⊗[k] H) :
    Coalgebra.counit (R := k) (contrRight φ s) =
      φ (contrLeft (Coalgebra.counit (R := k)) s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]
end GlobalTheory.LeftRightDerivations
